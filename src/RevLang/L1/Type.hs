{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE StandaloneDeriving   #-}

-- | L1, step 1: the finite type universe of the Π core calculus.
--
-- The Π family of reversible languages (James & Sabry, /Information
-- Effects/, POPL 2012) is a language of combinators witnessing type
-- isomorphisms.  The types themselves are the finite types generated
-- from the empty type, the unit type, binary sums and binary products;
-- categorically, @U@ presents the objects of the free symmetric rig
-- groupoid on one object (Choudhury, Karwowski & Sabry, /Symmetries in
-- Reversible Programming/, POPL 2022).
--
-- Values of these types form finite sets, which is what makes L1
-- exhaustively testable: every combinator's action can be checked on
-- /all/ of its inputs.
module RevLang.L1.Type
  ( -- * Type universe
    U (..)
    -- * Singletons
  , SU (..)
    -- * Cardinality
  , size
  ) where

-- | Type formers, used both as a value-level structure (via 'SU') and,
-- promoted, as indices for values and combinators.
data U
  = ZERO            -- ^ @0@ — the empty type (no values)
  | ONE             -- ^ @1@ — the unit type (one value)
  | PLUS  U U       -- ^ @τ ⊕ ν@ — binary sum
  | TIMES U U       -- ^ @τ ⊗ ν@ — binary product
  deriving (Eq, Ord, Show)

-- | Singleton for 'U': a value-level witness carrying a type-level
-- index.  Functions that need to case-analyse a type at runtime
-- (enumerating values, generating random values) take an @SU a@
-- rather than inspecting the phantom index.
data SU (a :: U) where
  SZERO  :: SU 'ZERO
  SONE   :: SU 'ONE
  SPLUS  :: SU a -> SU b -> SU ('PLUS a b)
  STIMES :: SU a -> SU b -> SU ('TIMES a b)

deriving instance Eq   (SU a)
deriving instance Show (SU a)

-- | Cardinality of a type: the number of values it has.
--
-- Isos must preserve cardinality (@size@ is invariant under every
-- combinator), a cheap sanity property the tests exploit.
size :: SU a -> Int
size SZERO         = 0
size SONE          = 1
size (SPLUS  a b)  = size a + size b
size (STIMES a b)  = size a * size b
