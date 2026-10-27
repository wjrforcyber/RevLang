-- | L2, step 2: the rewriting engine.
--
-- Three layers:
--
--   * 'rewriteTop' — try the rule list at the root of a term, first
--     match wins (rules are ordered cost-reducing first in 'axioms');
--   * 'stepEverywhere' — one bottom-up pass: recurse into the children
--     first, then attempt a root rewrite on the reassembled term;
--   * 'optimize' — iterate 'stepEverywhere' to a fixed point, so that
--     rewrites exposing new opportunities (e.g. interchange making a
--     cancellation adjacent) are caught by later passes.  The iteration
--     cap is a belt-and-braces guard: the current axioms are strictly
--     cost-reducing (involution, absorption, unit laws) or purely
--     structural with a single orientation (interchange), so cycles
--     are not expected — but an unbounded loop in an optimizer would
--     be an unacceptable failure mode.
--
-- Termination argument: involution, unit and absorption rewrites
-- strictly shrink the term (measured by 'cost' and by node count);
-- interchange rewrites preserve size but the kernel includes only one
-- orientation of each, so no rule can undo another's work.  The cap
-- covers any interaction this argument misses.
module RevLang.L2.Optimize
  ( rewriteTop
  , stepEverywhere
  , optimize
  ) where

import Data.Maybe (fromMaybe)

import RevLang.L1.Combinator (Pi (..))
import RevLang.L2.Rule (Rewrite (..), rwTry)

-- | Try every rule at the root; the first schema that matches wins.
rewriteTop :: [Rewrite] -> Pi a b -> Maybe (Pi a b)
rewriteTop rs c = go rs
  where
    go []        = Nothing
    go (r : rst) = case rwTry r c of
      Just c'  -> Just c'
      Nothing  -> go rst

-- | One bottom-up pass of the rule list over the whole term.
stepEverywhere :: [Rewrite] -> Pi a b -> Pi a b
stepEverywhere rs c = fromMaybe cRec (rewriteTop rs cRec)
  where
    cRec = case c of
      c1 :>>: c2 -> stepEverywhere rs c1 :>>: stepEverywhere rs c2
      c1 :**: c2 -> stepEverywhere rs c1 :**: stepEverywhere rs c2
      c1 :++: c2 -> stepEverywhere rs c1 :++: stepEverywhere rs c2
      _          -> c

-- | Rewrite to a fixed point (with an iteration cap).
maxPasses :: Int
maxPasses = 200

optimize :: [Rewrite] -> Pi a b -> Pi a b
optimize rs = go 0
  where
    go :: Int -> Pi a b -> Pi a b
    go n c
      | n >= maxPasses = c
      | otherwise =
          let c' = stepEverywhere rs c
          in  if c' == c then c else go (n + 1) c'
