{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE EmptyCase  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE KindSignatures #-}

-- | L1, step 4: evaluation of 1-combinators.
--
-- @eval c v@ applies the bijection denoted by @c :: Pi a b@ to a value
-- @v :: Val a@.  The evaluator is total:
--
--  * every pattern that looks structurally partial (e.g. @'Unite0P'@
--    matching only @'VInr'@) is total because @Val 'ZERO@ is
--    uninhabited — GHC's coverage checker accepts the clauses and no
--    @error@ calls appear anywhere;
--  * evaluation never inspects types at runtime: the meaning of a
--    combinator is fixed by its syntax alone.
--
-- The backward direction is given by 'evalBack', which evaluates the
-- 'adjoint' term.  Together,
--
-- > eval c >>> evalBack c == id   and   evalBack c >>> eval c == id
--
-- on all inputs — this is the bijection property, checked exhaustively
-- by the test suite (types are finite, so checking /all/ inputs is
-- decidable and cheap for small types).
module RevLang.L1.Eval
  ( eval
  , evalBack
  ) where

import RevLang.L1.Combinator (Pi (..), adjoint)
import RevLang.L1.Type (U (..))
import RevLang.L1.Value (Val (..))

-- | @Val 'ZERO@ is uninhabited, so this function has no possible
-- inputs; it lets the evaluator handle 'Unite0P' totally.
absurdZero :: Val 'ZERO -> b
absurdZero v = case v of {}

-- | Apply the bijection denoted by a combinator.
eval :: Pi a b -> Val a -> Val b
eval Id v = v

-- ⊕ structure
eval SwapP (VInl v) = VInr v
eval SwapP (VInr v) = VInl v
eval AssocP (VInl v)           = VInl (VInl v)
eval AssocP (VInr (VInl v))    = VInl (VInr v)
eval AssocP (VInr (VInr v))    = VInr v
eval AssocPI (VInl (VInl v))   = VInl v
eval AssocPI (VInl (VInr v))   = VInr (VInl v)
eval AssocPI (VInr v)          = VInr (VInr v)
eval Unite0P (VInr v)          = v
eval Unite0P (VInl z)          = absurdZero z
eval UnitiP v                  = VInr v

-- ⊗ structure
eval SwapT (VPair x y)           = VPair y x
eval AssocT (VPair x (VPair y z)) = VPair (VPair x y) z
eval AssocTI (VPair (VPair x y) z) = VPair x (VPair y z)
eval Unite1T (VPair VUnit v)     = v
eval UnitiT v                    = VPair VUnit v

-- distributivity
eval Dist (VPair (VInl x) y)     = VInl (VPair x y)
eval Dist (VPair (VInr x) y)     = VInr (VPair x y)
eval Factor (VInl (VPair x y))   = VPair (VInl x) y
eval Factor (VInr (VPair x y))   = VPair (VInr x) y

-- structure
eval (c1 :>>: c2) v              = eval c2 (eval c1 v)
eval (c1 :**: c2) (VPair x y)    = VPair (eval c1 x) (eval c2 y)
eval (c1 :++: _) (VInl x)       = VInl (eval c1 x)
eval (_ :++: c2) (VInr x)       = VInr (eval c2 x)

-- | Run a combinator backwards: @evalBack c = eval (adjoint c)@.
evalBack :: Pi a b -> Val b -> Val a
evalBack c = eval (adjoint c)
