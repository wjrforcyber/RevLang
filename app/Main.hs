module Main (main) where

import Control.Monad (when)

import RevLang.L1.Combinator (Pi (..), cost)
import RevLang.L1.Eval (eval, evalBack)
import RevLang.L1.Examples
  ( Bit, Eight, Four, c3not, cnot, flattenBitPair, flattenBitTriple
  , notC, permEight, permFour, toffoli, toffoliMct )
import RevLang.L1.Pretty (prettyPi, prettyU, prettyVal)
import RevLang.L1.Type (SU (..), U (..), size)
import RevLang.L1.Value (enumerate)
import RevLang.L2.Canon (Reg, SomeFlatten (..), flatten, reg2, reg4, regBits)
import RevLang.L2.Optimize (optimize)
import RevLang.L2.Rule (axioms)

-- | Print each L1 example: its term, cost, and full truth table with
-- the backward run, plus an exhaustive round-trip check.
main :: IO ()
main = do
  putStrLn "RevLang L1 — the Π core calculus (demo)"
  putStrLn "====================================="
  putStrLn ""
  demo "NOT : a ↦ ¬a"
    sBit uBit sBit uBit notC
  demo "CNOT : (a, b) ↦ (a, a ⊕ b)"
    sBitPair uBitPair sBitPair uBitPair cnot
  demo "Toffoli : (a, b, c) ↦ (a, b, c ⊕ (a ∧ b))"
    sBitTriple uBitTriple sBitTriple uBitTriple toffoli
  demo "MCT-Toffoli (control-tree construction; same bijection, cheaper term)"
    sBitTriple uBitTriple sBitTriple uBitTriple toffoliMct
  demo "C3NOT (3-control Toffoli) : (a, b, c, d) ↦ (a, b, c, d ⊕ (a ∧ b ∧ c))"
    sBitQuad uBitQuad sBitQuad uBitQuad c3not
  demo "flatten a bit pair to canonical form"
    sBitPair uBitPair sFour uFour flattenBitPair
  demo "flatten a bit triple to canonical form"
    sBitTriple uBitTriple sEight uEight flattenBitTriple
  demo "permute the canonical form (swap flat indices 2, 3)"
    sFour uFour sFour uFour permFour
  demo "permute the canonical form (swap flat indices 6, 7)"
    sEight uEight sEight uEight permEight

  putStrLn "L2 optimizer (local rewriting; every output re-validated by eval)"
  putStrLn ""
  demoL2 "CNOT" sBitPair cnot
  demoL2 "Toffoli" sBitTriple toffoli
  demoL2 "MCT-Toffoli" sBitTriple toffoliMct
  demoL2 "C3NOT" sBitQuad c3not
  demoL2 "NOT with a redundant swap detour"
    sBit (notC :>>: (notC :>>: notC) :>>: notC)

  putStrLn "L2.1a canonical flattening (generic)"
  putStrLn ""
  demoFlatten "generic flatten, 2-bit register (compare: hand-written, cost 4)" reg2 sBitPair
  demoFlatten "generic flatten, 4-bit register (no hand-written version exists)" reg4 sBitQuad
  where
    sBit = SPLUS SONE SONE :: SU Bit
    uBit = PLUS ONE ONE :: U

    sBitPair = STIMES sBit sBit
    uBitPair = TIMES uBit uBit

    sBitTriple = STIMES sBitPair sBit
    uBitTriple = TIMES uBitPair uBit

    sBitQuad = STIMES sBitTriple sBit
    uBitQuad = TIMES uBitTriple uBit

    sFour = SPLUS SONE (SPLUS SONE (SPLUS SONE SONE)) :: SU Four
    uFour = PLUS ONE (PLUS ONE (PLUS ONE ONE)) :: U

    sEight = SPLUS SONE (SPLUS SONE (SPLUS SONE (SPLUS SONE (SPLUS SONE (SPLUS SONE (SPLUS SONE SONE)))))) :: SU Eight
    uEight = PLUS ONE (PLUS ONE (PLUS ONE (PLUS ONE (PLUS ONE (PLUS ONE (PLUS ONE ONE)))))) :: U

demo :: String -> SU a -> U -> SU b -> U -> Pi a b -> IO ()
demo name sa ua _sb ub c = do
  putStrLn ("== " ++ name)
  putStrLn ("   type : " ++ prettyU ua ++ "  ↔  " ++ prettyU ub)
  putStrLn ("   term : " ++ prettyPi c)
  putStrLn ("   cost : " ++ show (cost c) ++ " primitives")
  mapM_ row (enumerate sa)
  let ok = all (\v -> evalBack c (eval c v) == v) (enumerate sa)
  putStrLn ("   round-trip on all " ++ show (size sa) ++ " inputs: "
            ++ (if ok then "OK" else "FAIL"))
  putStrLn ""
  where
    row v = putStrLn ("   " ++ pad 12 (prettyVal v) ++ " ↦ "
                      ++ pad 12 (prettyVal (eval c v)) ++ "  back: "
                      ++ prettyVal (evalBack c (eval c v)))

    pad n s = s ++ replicate (n - length s) ' '

-- | L2 section: report the optimizer's effect on one gate — cost
-- before → after, the optimized term when it changed, and an
-- exhaustive semantic re-validation against the original.
demoL2 :: String -> SU a -> Pi a b -> IO ()
demoL2 name sa c = do
  let c' = optimize axioms c
  putStrLn ("== " ++ name)
  putStrLn ("   cost : " ++ show (cost c) ++ " → " ++ show (cost c') ++ " primitives")
  when (c' /= c) $
    putStrLn ("   optimized : " ++ prettyPi c')
  let ok = all (\v -> eval c' v == eval c v) (enumerate sa)
  putStrLn ("   semantics preserved: " ++ (if ok then "OK" else "FAIL"))
  putStrLn ""

-- | L2.1a section: report one generic flattening — target size, term
-- cost, and an exhaustive round-trip check.
demoFlatten :: String -> Reg s -> SU s -> IO ()
demoFlatten name reg sa = case flatten reg of
  SomeFlatten st _ f -> do
    putStrLn ("== " ++ name)
    putStrLn ("   target size : " ++ show (size st)
              ++ "  (expected 2^" ++ show (regBits reg) ++ ")")
    putStrLn ("   term cost   : " ++ show (cost f) ++ " primitives")
    putStrLn ("   term        : " ++ prettyPi f)
    let ok = all (\v -> evalBack f (eval f v) == v) (enumerate sa)
    putStrLn ("   round-trip on all " ++ show (size sa) ++ " inputs: "
              ++ (if ok then "OK" else "FAIL"))
    putStrLn ""
