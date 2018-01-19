module Main where
import Prot.Lang.Lang
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Analyze
import Prot.Examples.Rotate
import Data.SBV
import Data.Parameterized.Context as Ctx
import qualified Prot.Lang.SMT as SMT
import qualified Prot.Examples.RPS as RPS
import qualified Prot.MPS.Process as Pr
import qualified Prot.MPS.ProcessNew as PN

{-
tstTuple :: Prog
tstTuple = do
    let d = mkDistr "D" (TTupleRepr (Ctx.empty Ctx.%> TIntRepr Ctx.%> TIntRepr)) (\_ _ -> [])
    xt <- bSampl d []
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
    x <- bSampl d []
    bIte (x |===| (enumLit A))
     (bRet (3 :: Expr TInt))
     (bRet (4 :: Expr TInt))
-}


main :: IO ()
main = do
    --putStrLn "hi"
    --putStrLn $ show $ sizeOfDist RPS.distOut
    --putStrLn . show =<< numLeaves (RPS.distOut)
    --putStrLn =<< ppDistDag (RPS.distOut)
    --putStrLn . show =<< distEquiv (RPS.fAddOut) (RPS.fAddOut)
    putStrLn . show =<< distEquiv rotateA rotateB

    --putStrLn $ ppProgDag (tstCommand "D" "x")
    --putStrLn =<< ppSatProgLeaves rotateA
    --putStrLn =<< ppSatProgLeaves rotateB
    --putStrLn =<< ppSatProgLeaves RPS.pingPongProg
    --putStrLn "A:"
    --putStrLn $ ppProgDag rotateA
    --putStrLn "B:"
    --putStrLn $ ppProgDag rotateB
    --putStrLn . show =<< runProg (tstCommand "x")
    --putStrLn . show =<< progsEquiv (tstCommand "D" "x") (tstCommand "D'" "y") 
    --putStrLn . show =<< progsEquiv (tstTuple "x") (tstTuple "y")
    --putStrLn . show =<< progsEquiv rotateA rotateB
    --putStrLn . show =<< distEquiv rotateA rotateB

