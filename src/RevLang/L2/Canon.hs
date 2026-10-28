{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}

-- | L2.1a: generic canonical flattening.
--
-- L1's examples hand-wrote a flattening per register width
-- ('RevLang.L1.Examples.flattenBitPair', 'flattenBitTriple').  This
-- module replaces them with one recursion, generic in the register.
--
-- == The design, and the one insight behind it
--
-- A canonical form needs to guarantee two things:
--
--   1. flattening is a bijection, and
--   2. the /enumerate order/ of the canonical form is the binary
--      numbering order — flat index = 2a+b, 4a+2b+c, … — because that
--      alignment is what makes \"a gate = a transposition of positions\"
--      true, which is the whole foundation of the L2.1 permutation
--      machinery.
--
-- Notably /absent/ from this list: the bracketing of the sum.
-- @(1⊕1)⊕(1⊕1)@ and @1⊕(1⊕(1⊕1))@ enumerate in identical order
-- ('RevLang.L1.Value.enumerate' concatenates left-then-right at any
-- bracketing).  Realizing this deletes the right-association cascade
-- ('assoc+⁻¹' chains) from the construction entirely: the canonical
-- form of L2.1 is a /split tree/ — any bracketing of a sum of unit
-- leaves — witnessed by 'Split'.
--
-- == The pieces
--
--   * 'Reg'  — witnesses \"@s@ is a product of bits\" (the input side);
--   * 'Split' — witnesses \"@t@ is a sum-tree of unit leaves\" (the
--     canonical side);
--   * 'distAll' — the two-clause recursion that distributes a product
--     of canonical sums: a leaf becomes 'Unite1T', a split becomes
--     'Dist' followed by recursion in both branches; its result type
--     is computed by the type family 'SplitTimes';
--   * 'flatten' — one recursion over a 'Reg', packaging the target
--     singleton, the target 'Split' witness, and the term (the target
--     type is /computed/, so it travels existentially in
--     'SomeFlatten').
--
-- The singleton, witness, and term recursions grow in lockstep — the
-- same discipline as L1's @SU@/@Val@/@Pi@ trio.
module RevLang.L2.Canon
  ( -- * Register witness (input side)
    Reg (..)
  , regBits
  , reg2
  , reg3
  , reg4
    -- * Canonical-form witness (output side)
  , Split (..)
  , splitLeaves
    -- * Generic flattening
  , SomeFlatten (..)
  , flatten
  , distAll
  ) where

import RevLang.L1.Combinator (Pi (..))
import RevLang.L1.Type (SU (..), U (..))

import RevLang.L1.Examples (Bit)

--------------------------------------------------------------------------------
-- Register witness: s is a product of bits
--------------------------------------------------------------------------------

-- | Witness that @s@ is a product of bits — the registers the
-- flattening accepts.  Any bracketing is allowed; the number of bits
-- is 'regBits'.
data Reg (s :: U) where
  RBit   :: Reg Bit                       -- ^ one bit: @1 ⊕ 1@
  RTimes :: Reg x -> Reg y -> Reg ('TIMES x y)

-- | Number of bits in the register.
regBits :: Reg s -> Int
regBits RBit         = 1
regBits (RTimes a b) = regBits a + regBits b

-- | Concrete register witnesses for the demo and test suite.
reg2 :: Reg ('TIMES Bit Bit)
reg2 = RTimes RBit RBit

reg3 :: Reg ('TIMES ('TIMES Bit Bit) Bit)
reg3 = RTimes reg2 RBit

reg4 :: Reg ('TIMES ('TIMES ('TIMES Bit Bit) Bit) Bit)
reg4 = RTimes reg3 RBit

--------------------------------------------------------------------------------
-- Canonical-form witness: t is a sum-tree of unit leaves
--------------------------------------------------------------------------------

-- | Witness that @t@ is a sum-tree of unit leaves — /any/ bracketing.
-- What matters for canonicality is the enumerate order, which is the
-- same for every bracketing; the witness just documents the shape so
-- the recursions can walk it.
data Split (t :: U) where
  SLeaf  :: Split 'ONE
  SSplit :: Split x -> Split y -> Split ('PLUS x y)

-- | Number of unit leaves of the witnessed sum — for a canonical form
-- of a register this is @2 ^ regBits@ (checked by the test suite).
splitLeaves :: Split t -> Int
splitLeaves SLeaf         = 1
splitLeaves (SSplit a b)  = splitLeaves a + splitLeaves b

--------------------------------------------------------------------------------
-- Distributing a product of canonical sums
--------------------------------------------------------------------------------

-- | The canonical form of @sx ⊗ sy@: distribute the left sum over the
-- right factor, recursively.  Two equations, mirroring 'Split'.
type family SplitTimes (sx :: U) (sy :: U) :: U where
  SplitTimes ('PLUS p q) sy = 'PLUS (SplitTimes p sy) (SplitTimes q sy)
  SplitTimes 'ONE sy        = sy

-- | The singleton of 'SplitTimes', built in lockstep with the family.
splitTimesSU :: Split sx -> SU sy -> SU (SplitTimes sx sy)
splitTimesSU SLeaf         sy = sy
splitTimesSU (SSplit a b)  sy = SPLUS (splitTimesSU a sy) (splitTimesSU b sy)

-- | The 'Split' witness of 'SplitTimes', likewise.
splitTimesSplit :: Split sx -> Split sy -> Split (SplitTimes sx sy)
splitTimesSplit SLeaf        wy = wy
splitTimesSplit (SSplit a b) wy = SSplit (splitTimesSplit a wy)
                                         (splitTimesSplit b wy)

-- | Distribute a canonical sum (left factor) over a type (right
-- factor): @sx ⊗ sy ↔ canonical (sx ⊗ sy)@.
--
-- The two clauses are the entire algorithm:
--
--   * leaf: @1 ⊗ sy ↔ sy@ — nothing to distribute, just drop the unit;
--   * split: 'Dist' peels the top split, recursion handles both
--     branches independently.
--
-- The enumerate order of the result is the binary order of the pair:
-- the left summand accounts for all low-left values, the right
-- summand for the rest — exactly the alignment property the
-- permutation machinery of L2.1b relies on.
distAll :: forall sx sy. Split sx -> SU sy -> Pi ('TIMES sx sy) (SplitTimes sx sy)
distAll SLeaf        _sy = Unite1T   -- refined: sx ~ ONE, so 1 ⊗ sy ↔ sy
distAll (SSplit a b) sy = Dist :>>: (distAll a sy :++: distAll b sy)

--------------------------------------------------------------------------------
-- Generic flattening
--------------------------------------------------------------------------------

-- | A flattening of register @s@: since the canonical target type is
-- /computed/, it travels existentially together with its singleton
-- and its 'Split' witness.
data SomeFlatten (s :: U) = forall t. SomeFlatten (SU t) (Split t) (Pi s t)

-- | Flatten any bit register to its canonical form.
--
-- One bit is already canonical (@Bit = 1 ⊕ 1@ is a two-leaf split), so
-- the base case is the identity.  A product flattens both halves and
-- finishes with 'distAll'.
flatten :: Reg s -> SomeFlatten s
flatten RBit = SomeFlatten (SPLUS SONE SONE) (SSplit SLeaf SLeaf) Id
flatten (RTimes rx ry) = case (flatten rx, flatten ry) of
  (SomeFlatten _sx wx fx, SomeFlatten sy wy fy) ->
    SomeFlatten (splitTimesSU wx sy)
                (splitTimesSplit wx wy)
                ((fx :**: fy) :>>: distAll wx sy)
