module Main where
import Prot.Lang.Lang
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Examples.Rotate
import Data.SBV
import Data.Parameterized.Context as Ctx

tstCommand :: String -> String -> Prog
tstCommand dname xname = do
    let d = mkDistr dname TIntRepr (\_ _ -> [])
    x <- bSampl xname d []
    bIte (x |<=| 5) 
        (do { bRet (x + 1) } )
        (do { bRet (x * 2) } )



main :: IO ()
main = do
    --putStrLn $ ppProgDag (tstCommand "D" "x")
    --putStrLn $ ppProgDag (tstCommand "D'" "y")
    putStrLn "A:"
    putStrLn $ ppProgDag rotateA
    putStrLn "B:"
    putStrLn $ ppProgDag rotateB
    --putStrLn =<< ppSatProgLeaves (tstCommand "x")
    --putStrLn . show =<< runProg (tstCommand "x")
    --putStrLn . show =<< progsEquiv (tstCommand "D" "x") (tstCommand "D'" "y") 
    putStrLn . show =<< progsEquiv rotateA rotateB
