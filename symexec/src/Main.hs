module Main where
import Prot.Lang.Lang
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Examples.Rotate
import Data.SBV
import Data.Parameterized.Context as Ctx


tstTuple :: String -> Prog
tstTuple xname = do
    let d = mkDistr "D" (TTupleRepr (Ctx.empty Ctx.%> TIntRepr Ctx.%> TIntRepr)) (\_ _ -> [])
    xt <- bSampl xname d []
    case ((getIth (mkSome xt) 0), (getIth (mkSome xt) 1)) of
      ((SomeExp TIntRepr x), (SomeExp TIntRepr y)) -> do
        bIte (x |<=| 5) 
            (do { unSome (mkTuple [mkSome x, mkSome y]) $ \_ e -> bRet e } )
            (do { unSome (mkTuple [mkSome y, mkSome x]) $ \_ e -> bRet e } )
      _ -> error "type error"

data MyEnum = A | B
mkSymbolicEnumeration ''MyEnum

tstEnum :: Prog
tstEnum = do
    let d = mkDistr "D" (TEnumRepr (TypeableType :: TypeableType MyEnum)) (\_ _ -> [])
    x <- bSampl "x" d []
    bIte (x |===| (enumLit A))
     (bRet (3 :: Expr TInt))
     (bRet (4 :: Expr TInt))



main :: IO ()
main = do
    --putStrLn $ ppProgDag (tstCommand "D" "x")
    --putStrLn $ ppProgDag (tstCommand "D'" "y")
    --putStrLn =<< ppSatProgLeaves rotateA
    --putStrLn =<< ppSatProgLeaves rotateB
    putStrLn =<< ppSatProgLeaves tstEnum
    --putStrLn "A:"
    --putStrLn $ ppProgDag rotateA
    --putStrLn "B:"
    --putStrLn $ ppProgDag rotateB
    --putStrLn . show =<< runProg (tstCommand "x")
    --putStrLn . show =<< progsEquiv (tstCommand "D" "x") (tstCommand "D'" "y") 
    --putStrLn . show =<< progsEquiv (tstTuple "x") (tstTuple "y")
    --putStrLn . show =<< progsEquiv rotateA rotateB
    putStrLn . show =<< progsEquiv tstEnum tstEnum

