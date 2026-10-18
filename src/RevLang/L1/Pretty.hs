{-# LANGUAGE GADTs #-}

-- | L1, step 5: readable rendering of types, terms and values.
--
-- The output style is /fully parenthesized/: every non-atomic node is
-- wrapped, so the rendering is unambiguous and diffs cleanly.  'Show'
-- instances remain machine-oriented; this module is for humans.
module RevLang.L1.Pretty
  ( prettyU
  , prettyPi
  , prettyVal
  ) where

import Data.List (intercalate)

import RevLang.L1.Combinator (Pi (..))
import RevLang.L1.Type (U (..))
import RevLang.L1.Value (Val (..))

-- | Types: @0@, @1@, @(τ ⊕ ν)@, @(τ ⊗ ν)@.
prettyU :: U -> String
prettyU ZERO        = "0"
prettyU ONE         = "1"
prettyU (PLUS  a b) = "(" ++ prettyU a ++ " ⊕ " ++ prettyU b ++ ")"
prettyU (TIMES a b) = "(" ++ prettyU a ++ " ⊗ " ++ prettyU b ++ ")"

-- | Combinator terms.
--
-- Composition chains are flattened (@a ; b ; c@ — unambiguous since
-- composition is associative); functorial terms are parenthesized
-- (@(f ⊗ g)@, @(f ⊕ g)@).  Primitive names use @+@/@×@ subscripts in
-- the obvious way, with @⁻¹@ marking inverse primitives.
prettyPi :: Pi a b -> String
prettyPi c0 = case c0 of
  Id        -> "id"
  SwapP     -> "swap+"
  AssocP    -> "assoc+"
  AssocPI   -> "assoc+⁻¹"
  Unite0P   -> "unite0+"
  UnitiP    -> "uniti0+"
  SwapT     -> "swap×"
  AssocT    -> "assoc×"
  AssocTI   -> "assoc×⁻¹"
  Unite1T   -> "unite1×"
  UnitiT    -> "uniti1×"
  Dist      -> "dist"
  Factor    -> "factor"
  _ :>>: _  -> intercalate " ; " (map atomAny (seqChain c0))
  c1 :**: c2 -> "(" ++ atom c1 ++ " ⊗ " ++ atom c2 ++ ")"
  c1 :++: c2 -> "(" ++ atom c1 ++ " ⊕ " ++ atom c2 ++ ")"
  where
    -- chain elements carry existentially quantified middle types
    seqChain :: Pi a b -> [AnyPi]
    seqChain (c1 :>>: c2) = seqChain c1 ++ seqChain c2
    seqChain c            = [AnyPi c]

    atom :: Pi a b -> String
    atom c = case c of
      _ :>>: _ -> "(" ++ prettyPi c ++ ")"
      _        -> prettyPi c

    atomAny (AnyPi c) = atom c

-- | An iso with its (hidden) endpoint types, used to flatten
-- composition chains for printing.
data AnyPi = forall x y. AnyPi (Pi x y)

-- | Values: @()@, @inl v@, @inr v@, @(v, w)@.
prettyVal :: Val a -> String
prettyVal VUnit        = "()"
prettyVal (VInl v)     = "inl " ++ injArg v
prettyVal (VInr v)     = "inr " ++ injArg v
prettyVal (VPair x y)  = "(" ++ prettyVal x ++ ", " ++ prettyVal y ++ ")"

-- | Argument of an injection: the unit value stays bare, composite
-- arguments are parenthesized so nesting reads unambiguously.
injArg :: Val a -> String
injArg VUnit        = "()"
injArg p@(VPair {}) = prettyVal p
injArg i@(VInl {})  = "(" ++ prettyVal i ++ ")"
injArg i@(VInr {})  = "(" ++ prettyVal i ++ ")"
