module Main where
import Prot.Lang.Lang
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command

tstCommand :: String -> Prog
tstCommand xname = do
    let d = mkDistr "D" TIntRepr (\_ _ -> [])
    x <- bSampl xname d []
    bIte (x |<=| 5) 
        (do { bIte (x |>| 7) 
            (do { bRet (x + 2) })
            (do { bRet (x + 2) })
           })
        (do { bRet (x * 3) })




main :: IO ()
main = do
    putStrLn $ ppProg (tstCommand "x")
    putStrLn $ ppProgLeaves (tstCommand "x")
    putStrLn =<< ppSatProgLeaves (tstCommand "x")
    --equiv <- progsEquiv (tstCommand "x") (tstCommand "y")
    --putStrLn equiv
