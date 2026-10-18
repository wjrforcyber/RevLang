{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeOperators        #-}

-- | L1, step 3: the 1-combinators of the Π core calculus.
--
-- A term of type @Pi a b@ is a witness that types @a@ and @b@ are
-- isomorphic; evaluating it (see "RevLang.L1.Eval") computes the
-- associated bijection @Val a -> Val b@.  Because terms can only be
-- built from isomorphisms, /every well-typed term denotes a bijection/
-- — the reversibility guarantee is a theorem of the type system, not a
-- runtime check.
--
-- The primitive generators follow the symmetric rig groupoid
-- presentation of Choudhury, Karwowski & Sabry (POPL 2022):
--
--  * @0@ is the unit of @⊕@ and @1@ is the unit of @⊗@
--    ('Unite0P' \/ 'UnitiP', 'Unite1T' \/ 'UnitiT');
--  * @⊕@ and @⊗@ are symmetric ('SwapP', 'SwapT');
--  * @⊕@ and @⊗@ are associative ('AssocP' \/ 'AssocPI',
--    'AssocT' \/ 'AssocTI');
--  * @⊗@ distributes over @⊕@ ('Dist' \/ 'Factor') — this is what
--    makes the structure a /rig/ (ring without negatives) groupoid;
--  * both connectives are functorial ('.:**:', '.:++:'), and terms
--    compose ('.:>>:').
--
-- Presentation choices made here (revisit when L2 fixes the
-- equational theory):
--
--  * inverses are named primitives ('AssocPI', 'Factor', …) instead of
--    an @Adj@ former.  Consequently 'adjoint' maps primitive to
--    primitive, is an involution on the nose, and the primitive-count
--    cost model of L2 needs no special case for adjoints.
--  * plus-functoriality @('.::+:')@ is kept primitive for
--    convenience; in a distributive rig groupoid it is derivable from
--    the other generators, so L2's rewriting may or may not treat it
--    as primitive.
module RevLang.L1.Combinator
  ( -- * Combinators
    Pi (..)
    -- * Adjoint
  , adjoint
    -- * Cost
  , cost
  ) where

import Numeric.Natural (Natural)
import RevLang.L1.Type (U (..))

infixr 1 :>>:
infixl 2 :**:, :++:

-- | Reversible combinators witnessing type isomorphisms @a ↔ b@.
data Pi (a :: U) (b :: U) where
  Id  :: Pi a a

  -- ⊕ structure ------------------------------------------------------
  SwapP    :: Pi ('PLUS a b) ('PLUS b a)
  AssocP   :: Pi ('PLUS a ('PLUS b c)) ('PLUS ('PLUS a b) c)
  AssocPI  :: Pi ('PLUS ('PLUS a b) c) ('PLUS a ('PLUS b c))
  Unite0P  :: Pi ('PLUS 'ZERO a) a
  UnitiP   :: Pi a ('PLUS 'ZERO a)

  -- ⊗ structure ------------------------------------------------------
  SwapT    :: Pi ('TIMES a b) ('TIMES b a)
  AssocT   :: Pi ('TIMES a ('TIMES b c)) ('TIMES ('TIMES a b) c)
  AssocTI  :: Pi ('TIMES ('TIMES a b) c) ('TIMES a ('TIMES b c))
  Unite1T  :: Pi ('TIMES 'ONE a) a
  UnitiT   :: Pi a ('TIMES 'ONE a)

  -- distributivity ---------------------------------------------------
  Dist     :: Pi ('TIMES ('PLUS a b) c) ('PLUS ('TIMES a c) ('TIMES b c))
  Factor   :: Pi ('PLUS ('TIMES a c) ('TIMES b c)) ('TIMES ('PLUS a b) c)

  -- structure --------------------------------------------------------
  (:>>:)   :: Pi a b -> Pi b c -> Pi a c                    -- ^ composition
  (:**:)   :: Pi a b -> Pi c d -> Pi ('TIMES a c) ('TIMES b d) -- ^ ×-functoriality
  (:++:)   :: Pi a b -> Pi c d -> Pi ('PLUS a c) ('PLUS b d) -- ^ ⊕-functoriality

deriving instance Show (Pi a b)

-- | Structural equality on terms, ignoring type indices (the indices
-- of sub-terms may legitimately differ, e.g. under ':>>:').  Derived
-- 'Eq' cannot be used here: GHC would need heterogeneous comparison
-- at the sub-term level.
instance Eq (Pi a b) where
  (==) = eqPi

eqPi :: Pi a b -> Pi c d -> Bool
eqPi Id Id = True
eqPi SwapP SwapP = True
eqPi AssocP AssocP = True
eqPi AssocPI AssocPI = True
eqPi Unite0P Unite0P = True
eqPi UnitiP UnitiP = True
eqPi SwapT SwapT = True
eqPi AssocT AssocT = True
eqPi AssocTI AssocTI = True
eqPi Unite1T Unite1T = True
eqPi UnitiT UnitiT = True
eqPi Dist Dist = True
eqPi Factor Factor = True
eqPi (a1 :>>: a2) (b1 :>>: b2) = eqPi a1 b1 && eqPi a2 b2
eqPi (a1 :**: a2) (b1 :**: b2) = eqPi a1 b1 && eqPi a2 b2
eqPi (a1 :++: a2) (b1 :++: b2) = eqPi a1 b1 && eqPi a2 b2
eqPi _ _ = False

-- | The adjoint @c† :: Pi b a@ of a combinator @c :: Pi a b@: the term
-- denoting the inverse bijection.
--
-- Composition order reverses; primitives map to their inverse
-- primitives.  'adjoint' is a syntactic involution,
-- @adjoint . adjoint = id@, which the test suite checks on random
-- terms.
adjoint :: Pi a b -> Pi b a
adjoint Id        = Id
adjoint SwapP     = SwapP
adjoint AssocP    = AssocPI
adjoint AssocPI   = AssocP
adjoint Unite0P   = UnitiP
adjoint UnitiP    = Unite0P
adjoint SwapT     = SwapT
adjoint AssocT    = AssocTI
adjoint AssocTI   = AssocT
adjoint Unite1T   = UnitiT
adjoint UnitiT    = Unite1T
adjoint Dist      = Factor
adjoint Factor    = Dist
adjoint (c1 :>>: c2) = adjoint c2 :>>: adjoint c1
adjoint (c1 :**: c2) = adjoint c1 :**: adjoint c2
adjoint (c1 :++: c2) = adjoint c1 :++: adjoint c2

-- | Number of primitive combinators in a term.
--
-- This is the placeholder cost model: L2's optimizer will minimize it
-- (rewriting to equivalent terms with fewer primitives), and will
-- likely refine it to weighted counts once there are measurements to
-- calibrate against.
cost :: Pi a b -> Natural
cost Id            = 0
cost SwapP         = 1
cost AssocP        = 1
cost AssocPI       = 1
cost Unite0P       = 1
cost UnitiP        = 1
cost SwapT         = 1
cost AssocT        = 1
cost AssocTI       = 1
cost Unite1T       = 1
cost UnitiT        = 1
cost Dist          = 1
cost Factor        = 1
cost (c1 :>>: c2)  = cost c1 + cost c2
cost (c1 :**: c2)  = cost c1 + cost c2
cost (c1 :++: c2)  = cost c1 + cost c2
