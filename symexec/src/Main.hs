module Main where
import Prot.Lang.Lang
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Examples.RPS
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
    putStrLn $ ppProgDag (tstCommand "D" "x")
    putStrLn $ ppProgDag (tstCommand "D'" "y")
    --putStrLn =<< ppSatProgLeaves (tstCommand "x")
    --putStrLn . show =<< runProg (tstCommand "x")
    equiv <- progsEquiv (tstCommand "D" "x") (tstCommand "D'" "y") -- TODO: this is currently failing instead of returning false.
    putStrLn $ show equiv
