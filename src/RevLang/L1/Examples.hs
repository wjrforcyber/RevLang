{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

-- | L1, step 6: flagship examples.
--
-- The NCT family (NOT, CNOT, Toffoli) and the MCT family
-- (multiple-controlled Toffoli) of reversible-logic synthesis.
--
-- The pattern used throughout is /flatten, permute, unflatten/:
--
--  1. /flatten/ a product of bits into a right-nested sum of units
--     (the canonical form of a finite set — its "binary counter");
--  2. /permute/ by applying a tiny structural combinator deep in the
--     tree (this is where group theory enters: a permutation of the
--     canonical form is just a term of the symmetric group);
--  3. /unflatten/ back with the adjoint of step 1.
--
-- This is exactly the normalization strategy of Choudhury, Karwowski &
-- Sabry (POPL 2022), so these examples are miniature rehearsals of
-- what the L2 optimizer will do automatically.
--
-- Note what /cannot/ be expressed: XOR or AND as functions
-- @Bit ⊗ Bit → Bit@ are not isomorphisms (they lose information), and
-- indeed no term of type @Pi ('TIMES Bit Bit) Bit@ exists.  Reversible
-- logic keeps the inputs: CNOT computes @(a, b) ↦ (a, a ⊕ b)@, and
-- Toffoli computes @(a, b, c) ↦ (a, b, c ⊕ (a ∧ b))@.
module RevLang.L1.Examples
  ( -- * Bit abbreviations
    Bit
  , Four
  , Eight
  , bit
  , unbit
    -- * Logic gates as isomorphisms
  , notC
  , cnot
  , toffoli    -- * Their building blocks
  , flattenBitPair
  , permFour
  , flattenBitTriple
  , permEight
    -- * MCT — the multiple-controlled Toffoli family
  , Counting (..)
  , cFour
  , cEight
  , mct
  , mctGate
  , toffoliMct
  , c3not
  ) where

import RevLang.L1.Combinator (Pi (..), adjoint)
import RevLang.L1.Type (U (..))
import RevLang.L1.Value (Val (..))

-- | A single bit: @Bit = 1 ⊕ 1@ with @false = inl ()@, @true = inr ()@.
type Bit = 'PLUS 'ONE 'ONE

-- | The right-nested 4-element type: @1 ⊕ 1 ⊕ 1 ⊕ 1@.
type Four = 'PLUS 'ONE ('PLUS 'ONE ('PLUS 'ONE 'ONE))

-- | The right-nested 8-element type.
type Eight = 'PLUS 'ONE ('PLUS 'ONE ('PLUS 'ONE ('PLUS 'ONE ('PLUS 'ONE ('PLUS 'ONE ('PLUS 'ONE 'ONE))))))

-- | Embed a Haskell 'Bool' as a 'Bit' value.
bit :: Bool -> Val Bit
bit False = VInl VUnit
bit True  = VInr VUnit

-- | Read a 'Bit' value back as a Haskell 'Bool'.
unbit :: Val Bit -> Bool
unbit (VInl _) = False
unbit (VInr _) = True

-- | NOT is literally the symmetry of ⊕: @swap+@ swaps the two bits.
notC :: Pi Bit Bit
notC = SwapP

-- | @Bit ⊗ Bit ↔ 1 ⊕ 1 ⊕ 1 ⊕ 1@: flatten a pair of bits to canonical
-- form, so flat index @2·a + b@ corresponds to the pair @(a, b)@.
--
-- > dist       :  (1⊕1) ⊗ Bit           ↔  (1 ⊗ Bit) ⊕ (1 ⊗ Bit)
-- > unite1× (each summand)
-- >            :                         ↔  Bit ⊕ Bit
-- > assoc+⁻¹   :  (1⊕1) ⊕ (1⊕1)         ↔  1 ⊕ 1 ⊕ 1 ⊕ 1
flattenBitPair :: Pi ('TIMES Bit Bit) Four
flattenBitPair =
       Dist
  :>>: (Unite1T :++: Unite1T)
  :>>: AssocPI

-- | Swap flat indices 2 and 3 of 'Four' (a transposition in the
-- symmetric group @S₄@): touch nothing for two levels, then swap.
permFour :: Pi Four Four
permFour = Id :++: (Id :++: SwapP)

-- | CNOT: @(a, b) ↦ (a, a ⊕ b)@.
--
-- As a permutation of the four flat values @00, 01, 10, 11@ (indexed
-- @0..3@ by @2a+b@), CNOT swaps @10 ↔ 11@ — exactly 'permFour'.
cnot :: Pi ('TIMES Bit Bit) ('TIMES Bit Bit)
cnot = flattenBitPair :>>: permFour :>>: adjoint flattenBitPair

-- | @Bit ⊗ Bit ⊗ Bit ↔ 1 ⊕ 1 ⊕ 1 ⊕ 1 ⊕ 1 ⊕ 1 ⊕ 1 ⊕ 1@.
--
-- Same strategy one level up: reassociate to @Bit ⊗ (Bit ⊗ Bit)@,
-- flatten the inner pair, distribute over the remaining bit, then
-- right-associate the summands.
flattenBitTriple :: Pi ('TIMES ('TIMES Bit Bit) Bit) Eight
flattenBitTriple =
       AssocTI                                    -- (a⊗b)⊗c  ↔  a⊗(b⊗c)
  :>>: (Id :**: flattenBitPair)                   --          ↔  a⊗Four
  :>>: Dist                                       --          ↔  (1⊗Four) ⊕ (1⊗Four)
  :>>: (Unite1T :++: Unite1T)                     --          ↔  Four ⊕ Four
  :>>: AssocPI                                    --          ↔  1⊕(3⊕Four)
  :>>: (Id :++: AssocPI)                          --          ↔  1⊕1⊕(2⊕Four)
  :>>: (Id :++: (Id :++: AssocPI))                --          ↔  Eight

-- | Swap flat indices 6 and 7 of 'Eight' (a transposition in @S₈@):
-- leave the first six levels alone, swap at the bottom pair.
permEight :: Pi Eight Eight
permEight = Id :++: (Id :++: (Id :++: (Id :++: (Id :++: (Id :++: SwapP)))))

-- | Toffoli: @(a, b, c) ↦ (a, b, c ⊕ (a ∧ b))@.
--
-- As a permutation of the eight flat values indexed @4a+2b+c@, it
-- swaps @110 ↔ 111@ (indices 6 and 7) — exactly 'permEight'.
toffoli :: Pi ('TIMES ('TIMES Bit Bit) Bit) ('TIMES ('TIMES Bit Bit) Bit)
toffoli = flattenBitTriple :>>: permEight :>>: adjoint flattenBitTriple

-- | Witness that @s@ is a right-nested sum of unit leaves — the
-- canonical carrier of flattened control patterns.  Unlike a plain
-- @SU s@ (which admits products, empty types, non-count sums, …),
-- @Counting s@ can only be built for the shapes @mct@ means to
-- consume, so the domain restriction is checked by the compiler.
data Counting (s :: U) where
  Two  :: Counting ('PLUS 'ONE 'ONE)          -- ^ 2 leaves — one control bit
  Plus :: Counting s -> Counting ('PLUS 'ONE s) -- ^ one leaf further up the spine

-- | Canonical counting witnesses for the register sizes used below.
cFour :: Counting Four
cFour = Plus (Plus Two)

cEight :: Counting Eight
cEight = Plus (Plus (Plus (Plus (Plus (Plus Two)))))

-- | MCT — the multiple-controlled Toffoli family, generic in the
-- number of controls.
--
-- @mct c@ acts on a register @s ⊗ Bit@ where @s@ is the flattened
-- pattern of @k@ control bits, leaf @i@ being the pattern with binary
-- value @i@.  The gate flips the target exactly on the all-ones
-- pattern, which is the deepest, rightmost leaf.
--
-- The recursion walks the /control tree/:
--
--   * 'Two' branches on the single control bit with @dist@: the zero
--     branch is a dead end (@id@ on the target), the one branch
--     carries the flip (@swap+@); @factor@ closes the branch;
--   * @'Plus' c@ branches likewise and recurses only down the one
--     branch — zero prefixes can never reach the all-ones pattern.
mct :: Counting s -> Pi ('TIMES s Bit) ('TIMES s Bit)
mct Two      = Dist :>>: (Id :**: Id) :++: (Id :**: SwapP) :>>: Factor
mct (Plus c) = Dist :>>: (Id :**: Id) :++: mct c :>>: Factor

-- | Lift 'mct' to a concrete register: @flattenC@ flattens the
-- control register @c@ (a product of bits) into its canonical sum
-- @s@.  The 'Counting' witness must agree with @flattenC@'s target
-- type, otherwise the composition does not typecheck — the mismatch
-- cannot be written.
mctGate :: Counting s -> Pi c s -> Pi ('TIMES c Bit) ('TIMES c Bit)
mctGate c flattenC =
  (flattenC :**: Id) :>>: mct c :>>: (adjoint flattenC :**: Id)

-- | Toffoli, rebuilt as MCT with two controls.  It denotes the same
-- bijection as 'toffoli' (checked exhaustively by the test suite)
-- but is a cheaper term — fewer primitives — a first concrete taste
-- of why term choice matters, i.e. of exactly what the L2 optimizer
-- will automate.
toffoliMct :: Pi ('TIMES ('TIMES Bit Bit) Bit) ('TIMES ('TIMES Bit Bit) Bit)
toffoliMct = mctGate cFour flattenBitPair

-- | C3NOT — MCT with three controls:
-- @(a, b, c, d) ↦ (a, b, c, d ⊕ (a ∧ b ∧ c))@.
c3not :: Pi ('TIMES ('TIMES ('TIMES Bit Bit) Bit) Bit) ('TIMES ('TIMES ('TIMES Bit Bit) Bit) Bit)
c3not = mctGate cEight flattenBitTriple
