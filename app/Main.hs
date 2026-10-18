module Main (main) where

import RevLang.L1.Combinator (Pi, cost)
import RevLang.L1.Eval (eval, evalBack)
import RevLang.L1.Examples
  ( Bit, Eight, Four, cnot, flattenBitPair, flattenBitTriple
  , notC, permEight, permFour, toffoli )
import RevLang.L1.Pretty (prettyPi, prettyU, prettyVal)
import RevLang.L1.Type (SU (..), U (..), size)
import RevLang.L1.Value (enumerate)

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
  demo "flatten a bit pair to canonical form"
    sBitPair uBitPair sFour uFour flattenBitPair
  demo "flatten a bit triple to canonical form"
    sBitTriple uBitTriple sEight uEight flattenBitTriple
  demo "permute the canonical form (swap flat indices 2, 3)"
    sFour uFour sFour uFour permFour
  demo "permute the canonical form (swap flat indices 6, 7)"
    sEight uEight sEight uEight permEight
  where
    sBit = SPLUS SONE SONE :: SU Bit
    uBit = PLUS ONE ONE :: U

    sBitPair = STIMES sBit sBit
    uBitPair = TIMES uBit uBit

    sBitTriple = STIMES sBitPair sBit
    uBitTriple = TIMES uBitPair uBit

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
