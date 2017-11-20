module Main where
import Prot.Lang.Lang
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Examples.RPS
import Data.Parameterized.Context as Ctx

tstCommand :: String -> Prog
tstCommand xname = do
    let d = mkDistr "D" (TTupleRepr (Ctx.empty Ctx.%> TIntRepr Ctx.%> TIntRepr)) (\_ _ -> [])
    xt <- bSampl xname d []
    case ((getIth (mkSomeExp xt) 0), (getIth (mkSomeExp xt) 1)) of
      ((SomeExp TIntRepr x), (SomeExp TIntRepr y)) -> do
        bIte (x |<=| 5) 
            (do { bRet x } )
            (do { bRet y } )




main :: IO ()
main = do
    putStrLn $ ppProg (tstCommand "x")
    putStrLn $ ppProgLeaves (tstCommand "x")
    --putStrLn =<< ppSatProgLeaves (tstCommand "x")
    putStrLn $ ppProg (rpsIdeal)
    putStrLn . show =<< runProg (tstCommand "x")
    --equiv <- progsEquiv (tstCommand "x") (tstCommand "y")
    --putStrLn equiv
