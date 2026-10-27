{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | L2, step 1: the trusted rewrite kernel.
--
-- A 'Rewrite' is a named schema that inspects a term at its root and,
-- when the schema's pattern matches, proposes a replacement.  The set
-- 'axioms' is the equational theory L2.0 works with — the 2-combinator
-- content in rule form.
--
-- Soundness discipline (LCF-style): the kernel is the only place
-- equations are asserted.  Each schema is individually justified —
-- either by the L1 bijection theorem (so no runtime check is needed)
-- or by a dedicated exhaustive test in the suite — and the optimizer
-- output is re-validated end-to-end against 'eval' on random terms.
-- Nothing else in L2 may invent an equation.
--
-- Scope note (L2.0): all schemas are /local/ — they only fire when the
-- pattern is contiguous in the term.  That is what makes them simple
-- and obviously sound, but it also bounds what they can achieve: the
-- flatten-permute-unflatten gates are locally irreducible because the
-- permutation separates the cancellable scaffolding.  Collapsing that
-- plumbing is a /global/ restructuring — normalization to canonical
-- form and permutation synthesis, per the POPL 2022 paper — and is
-- planned as L2.1 on top of this kernel.
module RevLang.L2.Rule
  ( -- * Rewrite schemas
    Rewrite (..)
  , axioms
    -- * The individual axioms
  , rwCancel
  , rwUnitL
  , rwUnitR
  , rwAbsorbTT
  , rwAbsorbPP
  , rwInterchangeT
  , rwInterchangeP
  ) where

import RevLang.L1.Combinator (Pi (..))

-- | A named, polymorphic rewrite schema: try to rewrite a term at its
-- root.  @Maybe@ signals "pattern did not match".
data Rewrite = Rewrite
  { rwName :: String
  , rwTry  :: forall a b. Pi a b -> Maybe (Pi a b)
  }

instance Show Rewrite where
  show = rwName

-- | The equational theory of L2.0, in application order: cost-reducing
-- schemas first, structural (cost-preserving) schemas last.
axioms :: [Rewrite]
axioms =
  [ rwCancel
  , rwUnitL
  , rwUnitR
  , rwAbsorbTT
  , rwAbsorbPP
  , rwInterchangeT
  , rwInterchangeP
  ]

-- | @p ; p† → id@ and @p† ; p → id@ for every primitive @p@.
--
-- This is the groupoid law — every generator of the calculus is an
-- isomorphism with its named adjoint — spelled out as 26 ground
-- patterns (13 primitives, both orientations).
--
-- A reviewer's question worth pausing on: why not one general rule
-- @c ; c† → id@ for arbitrary composite @c@, which is semantically
-- true by the L1 bijection theorem?  Because the pattern matcher
-- compares terms with '(==)', which ignores type indices; from a
-- match @c2 == adjoint c1@ on @c1 :: Pi a m@ and @c2 :: Pi m b@ the
-- typechecker cannot conclude @b ~ a@, so returning @Id :: Pi a b@
-- would be a type error.  Each ground clause below, by contrast,
-- carries its own proof: matching e.g. @(SwapP :>>: SwapP)@ visibly
-- has source and target of the same type, so @Just Id@ typechecks.
-- (Recovering the composite version needs proof-carrying terms —
-- 2-combinators with term-level indices — which is exactly the
-- planned Pi2 layer, where adjoint-matching becomes structural
-- pattern matching instead of equality testing.)
rwCancel :: Rewrite
rwCancel = Rewrite "cancel: p ; p† → id" try
  where
    -- The explicit signature is load-bearing: without it GHC tries to
    -- unify the result types of all clauses into one, but each clause
    -- refines the schema's variables to a different type shape.
    try :: forall a b. Pi a b -> Maybe (Pi a b)
    try (SwapP :>>: SwapP)    = Just Id
    try (SwapT :>>: SwapT)    = Just Id
    try (AssocP :>>: AssocPI) = Just Id
    try (AssocPI :>>: AssocP) = Just Id
    try (Unite0P :>>: UnitiP) = Just Id
    try (UnitiP :>>: Unite0P) = Just Id
    try (AssocT :>>: AssocTI) = Just Id
    try (AssocTI :>>: AssocT) = Just Id
    try (Unite1T :>>: UnitiT) = Just Id
    try (UnitiT :>>: Unite1T) = Just Id
    try (Dist :>>: Factor)    = Just Id
    try (Factor :>>: Dist)    = Just Id
    try _                     = Nothing

-- | @id ; c → c@.
rwUnitL :: Rewrite
rwUnitL = Rewrite "unit-left: id ; c → c" try
  where
    try :: forall a b. Pi a b -> Maybe (Pi a b)
    try (Id :>>: c) = Just c
    try _           = Nothing

-- | @c ; id → c@.
rwUnitR :: Rewrite
rwUnitR = Rewrite "unit-right: c ; id → c" try
  where
    try :: forall a b. Pi a b -> Maybe (Pi a b)
    try (c :>>: Id) = Just c
    try _           = Nothing

-- | @id ⊗ id → id@.
rwAbsorbTT :: Rewrite
rwAbsorbTT = Rewrite "absorb-id-×: id ⊗ id → id" try
  where
    try :: forall a b. Pi a b -> Maybe (Pi a b)
    try (Id :**: Id) = Just Id
    try _            = Nothing

-- | @id ⊕ id → id@.
rwAbsorbPP :: Rewrite
rwAbsorbPP = Rewrite "absorb-id-⊕: id ⊕ id → id" try
  where
    try :: forall a b. Pi a b -> Maybe (Pi a b)
    try (Id :++: Id) = Just Id
    try _            = Nothing

-- | Interchange for @⊗@ (horizontal composition):
--
-- > (f ⊗ g) ; (f' ⊗ g')  →  (f ; f') ⊗ (g ; g')
--
-- Cost-preserving but /enabling/: it lets cancellations that were
-- separated by parallel structure become adjacent.  Sound because both
-- sides run the four sub-bijections in the same causal order.
rwInterchangeT :: Rewrite
rwInterchangeT = Rewrite "interchange-×" try
  where
    try :: forall a b. Pi a b -> Maybe (Pi a b)
    try ((f :**: g) :>>: (f' :**: g')) = Just ((f :>>: f') :**: (g :>>: g'))
    try _                              = Nothing

-- | Interchange for @⊕@ (dispatch composition):
--
-- > (f ⊕ g) ; (f' ⊕ g')  →  (f ; f') ⊕ (g ; g')
--
-- Sound because both sides dispatch on the tag first and run the same
-- pair of sub-bijections.
rwInterchangeP :: Rewrite
rwInterchangeP = Rewrite "interchange-⊕" try
  where
    try :: forall a b. Pi a b -> Maybe (Pi a b)
    try ((f :++: g) :>>: (f' :++: g')) = Just ((f :>>: f') :++: (g :>>: g'))
    try _                              = Nothing
