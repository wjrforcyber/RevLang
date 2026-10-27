{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}

-- | L1, step 7: the test suite.
--
-- Strategy: because every L1 type is finite, /every property of a
-- combinator can be checked on all of its inputs/.  Three layers:
--
--  1. @enumerate@ laws — the bridge from types to lists is correct
--     (completeness, no duplicates, cardinality agreement);
--
--  2. random isomorphisms — 'genSomeIso' builds random well-typed
--     terms by starting from random primitive instantiations and
--     closing under composition (gated by singleton type equality),
--     tensor, ⊕-functoriality, and adjoint.  Terms are generated
--     /between different types/, since almost all primitives are
--     type-changing.  For every generated @c :: Pi a b@ we check,
--     exhaustively over @enumerate@:
--       * cardinalities agree,
--       * @evalBack c . eval c == id@ and @eval c . evalBack c == id@
--         (the bijection property), and
--       * @adjoint@ is a syntactic involution.
--
--     (No shrinking of random isos yet — failures report the seed.)
--
--  3. example semantics — NOT, CNOT, Toffoli compute what the truth
--     tables say, on all inputs, forwards and backwards.
module Main (main) where

import Data.List (nub)
import Data.Type.Equality ((:~:) (..))
import Test.QuickCheck (Gen, Property, (.&&.), (===), forAll, frequency, oneof, property)
import Test.Tasty
import Test.Tasty.QuickCheck

import RevLang.L1.Combinator (Pi (..), adjoint, cost)
import RevLang.L1.Eval (eval, evalBack)
import RevLang.L1.Examples (Bit, Eight, Four, bit, c3not, cnot, flattenBitPair, flattenBitTriple, notC, permEight, permFour, toffoli, toffoliMct)
import RevLang.L1.Type (SU (..), U (..), size)
import RevLang.L1.Value (Val (..), enumerate)
import RevLang.L2.Optimize (optimize, rewriteTop)
import RevLang.L2.Rule (axioms)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "RevLang L1"
  [ testGroup "enumerate"
      [ testProperty "length ≡ cardinality"  propEnumLen
      , testProperty "values are distinct"   propEnumNub
      ]
  , testGroup "random isomorphisms"
      [ testProperty "eval is a bijection (exhaustive)"   propBijection
      , testProperty "adjoint is an involution"           propAdjointInvolution
      , testProperty "cardinality is preserved"           propSizeInvariant
      ]
  , testGroup "examples"
      [ testProperty "NOT semantics"        notCheck
      , testProperty "CNOT semantics"       cnotCheck
      , testProperty "Toffoli semantics"    toffoliCheck
      , testProperty "MCT-Toffoli ≡ Toffoli"      mctToffoliCheck
      , testProperty "C3NOT semantics"            c3notCheck
      , testProperty "MCT term is cheaper than flatten-permute" costMctCheck
      , testProperty "flatten/unflatten are inverse (pairs)"    flattenPairCheck
      , testProperty "flatten/unflatten are inverse (triples)"  flattenTripleCheck
      , testProperty "permutations round-trip"                  permCheck
      , testProperty "costs are sensible"                       costCheck
      ]
  , testGroup "L2 rewriter"
      [ testProperty "optimizer preserves semantics (random)"  propOptimizerSound
      , testProperty "optimizer never increases cost (random)" propOptimizerMonotone
      , testProperty "optimizer is idempotent (random)"        propOptimizerIdempotent
      , testProperty "cancel rule fires on p ; p†"             cancelRuleCheck
      , testProperty "interchange-× is semantically sound"     interchangeCheck
      , gateProp "optimizer preserves NOT"         sBit notC
      , gateProp "optimizer preserves CNOT"        sBitPair cnot
      , gateProp "optimizer preserves Toffoli"     sBitTriple toffoli
      , gateProp "optimizer preserves MCT-Toffoli" sBitTriple toffoliMct
      , gateProp "optimizer preserves C3NOT"       sBitQuad c3not
      , testProperty "detoured NOT annihilates to identity"    detourCheck
      ]
  ]

--------------------------------------------------------------------------------
-- Random types
--------------------------------------------------------------------------------

data SomeU = forall a. SomeU (SU a)

instance Show SomeU where
  show (SomeU sa) = "type of size " ++ show (size sa)

-- | Draw a continuation with an existentially quantified singleton.
withU :: Gen SomeU -> (forall x. SU x -> Gen r) -> Gen r
withU g k = g >>= \u -> case u of SomeU a -> k a

-- | Random type of bounded height.  Height bounds keep exhaustive
-- checks cheap: height 5 products are at most 32 elements.
genU :: Int -> Gen SomeU
genU 0 = oneof [pure (SomeU SZERO), pure (SomeU SONE)]
genU n = frequency
  [ (1, pure (SomeU SZERO))
  , (3, pure (SomeU SONE))
  , (3, withU (genU n1) $ \a -> withU (genU n1) $ \b -> pure (SomeU (SPLUS a b)))
  , (3, withU (genU n1) $ \a -> withU (genU n1) $ \b -> pure (SomeU (STIMES a b)))
  ]
  where
    n1 = n `div` 2

-- | Singleton type equality, needed to gate composition of random
-- isos (terms compose only when the middle types agree).
eqSU :: SU a -> SU b -> Maybe (a :~: b)
eqSU SZERO        SZERO        = Just Refl
eqSU SONE         SONE         = Just Refl
eqSU (SPLUS  a b) (SPLUS  c d) = case (eqSU a c, eqSU b d) of
  (Just Refl, Just Refl) -> Just Refl
  _                      -> Nothing
eqSU (STIMES a b) (STIMES c d) = case (eqSU a c, eqSU b d) of
  (Just Refl, Just Refl) -> Just Refl
  _                      -> Nothing
eqSU _            _            = Nothing

--------------------------------------------------------------------------------
-- Random isomorphisms
--------------------------------------------------------------------------------

data SomeIso = forall a b. SomeIso (SU a) (SU b) (Pi a b)

instance Show SomeIso where
  show (SomeIso sa sb _) =
    "iso between types of size " ++ show (size sa) ++ " and " ++ show (size sb)

-- | A random primitive at random sub-types: one instantiation of each
-- generator of the calculus.
genPrimIso :: Gen SomeIso
genPrimIso = oneof
  [ withU su $ \a -> withU su $ \b ->
      pure (SomeIso (SPLUS a b) (SPLUS b a) SwapP)
  , withU su $ \a -> withU su $ \b -> withU su $ \c ->
      pure (SomeIso (SPLUS a (SPLUS b c)) (SPLUS (SPLUS a b) c) AssocP)
  , withU su $ \a -> withU su $ \b -> withU su $ \c ->
      pure (SomeIso (SPLUS (SPLUS a b) c) (SPLUS a (SPLUS b c)) AssocPI)
  , withU su $ \a ->
      pure (SomeIso (SPLUS SZERO a) a Unite0P)
  , withU su $ \a ->
      pure (SomeIso a (SPLUS SZERO a) UnitiP)
  , withU su $ \a -> withU su $ \b ->
      pure (SomeIso (STIMES a b) (STIMES b a) SwapT)
  , withU su $ \a -> withU su $ \b -> withU su $ \c ->
      pure (SomeIso (STIMES a (STIMES b c)) (STIMES (STIMES a b) c) AssocT)
  , withU su $ \a -> withU su $ \b -> withU su $ \c ->
      pure (SomeIso (STIMES (STIMES a b) c) (STIMES a (STIMES b c)) AssocTI)
  , withU su $ \a ->
      pure (SomeIso (STIMES SONE a) a Unite1T)
  , withU su $ \a ->
      pure (SomeIso a (STIMES SONE a) UnitiT)
  , withU su $ \a -> withU su $ \b -> withU su $ \c ->
      pure (SomeIso (STIMES (SPLUS a b) c) (SPLUS (STIMES a c) (STIMES b c)) Dist)
  , withU su $ \a -> withU su $ \b -> withU su $ \c ->
      pure (SomeIso (SPLUS (STIMES a c) (STIMES b c)) (STIMES (SPLUS a b) c) Factor)
  , withU su $ \a ->
      pure (SomeIso a a Id)
  ]
  where
    su = genU 3

-- | Random well-typed iso: primitives closed under adjoint, tensor,
-- ⊕-functoriality, and composition (rejection-sampled until the middle
-- types match, with a bounded number of attempts).
genSomeIso :: Int -> Gen SomeIso
genSomeIso 0 = genPrimIso
genSomeIso n = frequency
  [ (3, genPrimIso)
  , (2, genAdj)
  , (2, genTensor)
  , (2, genPlusF)
  , (4, genCompose)
  ]
  where
    n1 = n `div` 2

    genAdj = do
      si <- genSomeIso n1
      case si of
        SomeIso s t c -> pure (SomeIso t s (adjoint c))

    genTensor = do
      si1 <- genSomeIso n1
      si2 <- genSomeIso n1
      case (si1, si2) of
        (SomeIso s1 t1 c1, SomeIso s2 t2 c2) ->
          pure (SomeIso (STIMES s1 s2) (STIMES t1 t2) (c1 :**: c2))

    genPlusF = do
      si1 <- genSomeIso n1
      si2 <- genSomeIso n1
      case (si1, si2) of
        (SomeIso s1 t1 c1, SomeIso s2 t2 c2) ->
          pure (SomeIso (SPLUS s1 s2) (SPLUS t1 t2) (c1 :++: c2))

    genCompose = do
      si1 <- genSomeIso n1
      case si1 of
        SomeIso s1 t1 c1 -> do
          mNext <- tryFrom t1 8
          case mNext of
            Nothing           -> pure si1
            Just (SomeIsoFrom c2 t2) -> pure (SomeIso s1 t2 (c1 :>>: c2))

-- | Generate an iso whose source is the given type; proof of the match
-- is the 'castWith' inside.
data SomeIsoFrom t = forall b. SomeIsoFrom (Pi t b) (SU b)

tryFrom :: SU t -> Int -> Gen (Maybe (SomeIsoFrom t))
tryFrom _ 0 = pure Nothing
tryFrom st k = do
  si <- genPrimIso
  case si of
    SomeIso s2 t2 c2 -> case eqSU st s2 of
      -- Refl brings t ~ a into scope, so c2 :: Pi a b is accepted
      -- where Pi t b is expected
      Just Refl -> pure (Just (SomeIsoFrom c2 t2))
      Nothing   -> tryFrom st (k - 1)

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

propEnumLen :: Property
propEnumLen = forAll (genU 5) $ \u -> case u of
  SomeU sa -> length (enumerate sa) === size sa

propEnumNub :: Property
propEnumNub = forAll (genU 5) $ \u -> case u of
  SomeU sa -> length (nub (map show (enumerate sa))) === size sa

propBijection :: Property
propBijection = forAll (genSomeIso 5) $ \si -> case si of
  SomeIso sa sb c ->
    let fwd = all (\v -> evalBack c (eval c v) == v) (enumerate sa)
        bwd = all (\w -> eval c (evalBack c w) == w) (enumerate sb)
    in  property fwd .&&. property bwd

propAdjointInvolution :: Property
propAdjointInvolution = forAll (genSomeIso 5) $ \si -> case si of
  SomeIso _ _ c -> adjoint (adjoint c) === c

propSizeInvariant :: Property
propSizeInvariant = forAll (genSomeIso 5) $ \si -> case si of
  SomeIso sa sb _ -> size sa === size sb

--------------------------------------------------------------------------------
-- Example semantics (checked on every input)
--------------------------------------------------------------------------------

bits :: [Bool]
bits = [False, True]

notCheck :: Property
notCheck = property $
  all (\b -> eval notC (bit b) == bit (not b)) bits

cnotCheck :: Property
cnotCheck = property $
  all ( \(a, b) ->
          eval cnot (VPair (bit a) (bit b)) == VPair (bit a) (bit (a /= b)))
      [(a, b) | a <- bits, b <- bits]

toffoliCheck :: Property
toffoliCheck = property $
  all ( \(a, b, c) ->
          let inp = VPair (VPair (bit a) (bit b)) (bit c)
              out = VPair (VPair (bit a) (bit b)) (bit (c /= (a && b)))
          in  eval toffoli inp == out)
      [(a, b, c) | a <- bits, b <- bits, c <- bits]

-- | The control-tree MCT construction and the flatten-permute
-- construction denote the same bijection, on every input.
mctToffoliCheck :: Property
mctToffoliCheck = property $
  all (\v -> eval toffoliMct v == eval toffoli v) (enumerate sBitTriple)

c3notCheck :: Property
c3notCheck = property $
  all (\(a, b, c, d) ->
        let inp = VPair (VPair (VPair (bit a) (bit b)) (bit c)) (bit d)
            out = VPair (VPair (VPair (bit a) (bit b)) (bit c)) (bit (d /= (a && b && c)))
        in  eval c3not inp == out)
      [(a, b, c, d) | a <- bits, b <- bits, c <- bits, d <- bits]

costMctCheck :: Property
costMctCheck = property (cost toffoliMct < cost toffoli)

-- | flatten and its adjoint are mutual inverses, on every input, both
-- directions, for pairs and triples.
flattenPairCheck :: Property
flattenPairCheck = property $
  all (\v -> evalBack flattenBitPair (eval flattenBitPair v) == v)
      (enumerate sBitPair)
  && all (\w -> eval flattenBitPair (evalBack flattenBitPair w) == w)
         (enumerate sFour)

flattenTripleCheck :: Property
flattenTripleCheck = property $
  all (\v -> evalBack flattenBitTriple (eval flattenBitTriple v) == v)
      (enumerate sBitTriple)

permCheck :: Property
permCheck = property $
  all (\v -> evalBack permFour (eval permFour v) == v) (enumerate sFour)
  && all (\w -> evalBack permEight (eval permEight w) == w) (enumerate sEight)

costCheck :: Property
costCheck = property (cost (Id :: Pi Bit Bit) == 0 && cost cnot > 0 && cost toffoli > 0)

--------------------------------------------------------------------------------
-- L2 rewriter
--------------------------------------------------------------------------------

-- | The primary soundness property of L2.0: optimizing a random
-- isomorphism yields a term computing the same bijection, checked
-- exhaustively over the finite domain.  If any kernel rule were
-- unsound, this property would eventually catch it.
propOptimizerSound :: Property
propOptimizerSound = forAll (genSomeIso 5) $ \si -> case si of
  SomeIso sa _ c -> property $
    all (\v -> eval (optimize axioms c) v == eval c v) (enumerate sa)

propOptimizerMonotone :: Property
propOptimizerMonotone = forAll (genSomeIso 5) $ \si -> case si of
  SomeIso _ _ c -> cost (optimize axioms c) <= cost c

propOptimizerIdempotent :: Property
propOptimizerIdempotent = forAll (genSomeIso 5) $ \si -> case si of
  SomeIso _ _ c -> optimize axioms (optimize axioms c) == optimize axioms c

-- | The cancellation schema recognizes primitive adjoint pairs.
cancelRuleCheck :: Property
cancelRuleCheck = property $
  rewriteTop axioms (notC :>>: notC) == Just (Id :: Pi Bit Bit)

-- | Interchange on a concrete instance: composing two parallel pairs
-- equals pairing two sequential compositions, exhaustively over the
-- 9-element domain.
interchangeCheck :: Property
interchangeCheck = property $
  let lhs = (AssocP :**: AssocT) :>>: (AssocPI :**: AssocTI)
      rhs = (AssocP :>>: AssocPI) :**: (AssocT :>>: AssocTI)
      -- source type of lhs: (1⊕(1⊕1)) ⊗ (1⊗(1⊗1))
      dom = STIMES (SPLUS SONE (SPLUS SONE SONE))
                   (STIMES SONE (STIMES SONE SONE))
  in  all (\v -> eval lhs v == eval rhs v) (enumerate dom)

-- | Every gate's optimized form must compute the same bijection.
gateProp :: String -> SU a -> Pi a b -> TestTree
gateProp name sa c = testProperty name $ property $
  let c' = optimize axioms c
  in  all (\v -> eval c' v == eval c v) (enumerate sa)

-- | A NOT gate with a redundant swap detour optimizes to the identity:
-- @not ; swap ; swap ; not = id@, cost 4 → 0.  The showcase that the
-- fixpoint iteration composes several rules (cancel, then unit laws,
-- then cancel again).
detourCheck :: Property
detourCheck = property $
  let t  = notC :>>: (notC :>>: notC) :>>: notC
      t' = optimize axioms t
  in  cost t' == 0 .&&. t' == (Id :: Pi Bit Bit)

--------------------------------------------------------------------------------
-- Singletons for the example types (kept here, next to their uses)
--------------------------------------------------------------------------------

sBit :: SU Bit
sBit = SPLUS SONE SONE

sFour :: SU Four
sFour = SPLUS SONE (SPLUS SONE (SPLUS SONE SONE))

sEight :: SU Eight
sEight = SPLUS SONE (SPLUS SONE (SPLUS SONE (SPLUS SONE (SPLUS SONE (SPLUS SONE (SPLUS SONE SONE))))))

sBitPair :: SU ('TIMES Bit Bit)
sBitPair = STIMES sBit sBit

sBitTriple :: SU ('TIMES ('TIMES Bit Bit) Bit)
sBitTriple = STIMES sBitPair sBit

sBitQuad :: SU ('TIMES ('TIMES ('TIMES Bit Bit) Bit) Bit)
sBitQuad = STIMES sBitTriple sBit
