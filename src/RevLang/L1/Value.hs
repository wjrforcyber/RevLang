{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE StandaloneDeriving   #-}

-- | L1, step 2: values of the finite types of 'U'.
--
-- @ZERO@ is uninhabited (there is no constructor returning @Val 'ZERO@),
-- which is exactly what lets the evaluator be total: patterns that
-- would match a @Val 'ZERO@ are provably unreachable and GHC's
-- coverage checker knows it.
module RevLang.L1.Value
  ( -- * Values
    Val (..)
    -- * Enumeration
  , enumerate
  ) where

import RevLang.L1.Type (SU (..), U (..))

-- | Values of the finite types.  A @Val a@ is indexed by its type, so
-- a value of type @Val a@ is well-typed by construction.
data Val (a :: U) where
  VUnit  :: Val 'ONE                       -- ^ the single value of @1@
  VInl   :: Val a -> Val ('PLUS a b)       -- ^ left injection
  VInr   :: Val b -> Val ('PLUS a b)       -- ^ right injection
  VPair  :: Val a -> Val b -> Val ('TIMES a b) -- ^ pairing

deriving instance Show (Val a)

-- | Structural equality.  Written by hand rather than derived so the
-- (impossible) mixed-constructor cases are visible for review.
instance Eq (Val a) where
  VUnit       == VUnit        = True
  VInl  x     == VInl  y      = x == y
  VInr  x     == VInr  y      = x == y
  VPair x1 y1 == VPair x2 y2  = x1 == x2 && y1 == y2
  _           == _            = False

-- | All values of a finite type, in canonical (left-to-right) order.
--
-- For sums, left summands are listed before right ones; for products,
-- the right component varies fastest.  @enumerate@ is the bridge from
-- the typed world to plain lists: exhaustive testing of a combinator
-- @c :: Pi a b@ means checking its behaviour on @enumerate sa@.
enumerate :: SU a -> [Val a]
enumerate SZERO         = []
enumerate SONE          = [VUnit]
enumerate (SPLUS  a b)  = map VInl (enumerate a) ++ map VInr (enumerate b)
enumerate (STIMES a b)  = [VPair x y | x <- enumerate a, y <- enumerate b]
