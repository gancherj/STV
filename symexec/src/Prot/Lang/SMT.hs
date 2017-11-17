module Prot.Lang.SMT where
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Analyze
import Prot.Lang.Types
import Data.SBV
import Data.SBV.Control
import Data.Type.Equality
import Control.Monad
import qualified Data.Map.Strict as Map

type family Interp (tp :: Type) :: * where
    Interp TInt = Integer
    Interp TBool = Bool

data SomeSBV = forall tp. SomeSBV (TypeRepr tp) (SBV (Interp tp))

evalExpr :: Map.Map String (SomeSBV) -> Expr tp -> SBV (Interp tp)
evalExpr emap (AtomExpr (Atom x tr)) =
    case Map.lookup x emap of
      Just (SomeSBV tr2 e) ->
          case testEquality tr tr2 of
            Just Refl -> e
            _ -> error "type error"
      _ -> error "not found"

evalExpr emap (Expr (IntLit i)) = literal i
evalExpr emap (Expr (IntAdd e1 e2)) = (evalExpr emap e1) + (evalExpr emap e2)
evalExpr emap (Expr (IntMul e1 e2)) = (evalExpr emap e1) * (evalExpr emap e2)
evalExpr emap (Expr (IntNeg e1 )) = -(evalExpr emap e1) 

evalExpr emap (Expr (BoolLit b)) = literal b
evalExpr emap (Expr (BoolAnd b1 b2)) = (evalExpr emap b1) &&& (evalExpr emap b2)
evalExpr emap (Expr (BoolOr b1 b2)) = (evalExpr emap b1) ||| (evalExpr emap b2)
evalExpr emap (Expr (BoolXor b1 b2)) = (evalExpr emap b1) <+> (evalExpr emap b2)
evalExpr emap (Expr (BoolNot e1 )) = bnot (evalExpr emap e1) 

evalExpr emap (Expr (IntLe e1 e2)) = (evalExpr emap e1) .<= (evalExpr emap e2)
evalExpr emap (Expr (IntLt e1 e2)) = (evalExpr emap e1) .< (evalExpr emap e2)
evalExpr emap (Expr (IntGt e1 e2)) = (evalExpr emap e1) .> (evalExpr emap e2)
evalExpr emap (Expr (IntEq e1 e2)) = (evalExpr emap e1) .== (evalExpr emap e2)
evalExpr emap (Expr (IntNeq e1 e2)) = (evalExpr emap e1) ./= (evalExpr emap e2)

-- we do case analysis here to not require SymWord on tp
atomToSymVar :: Atom tp -> Symbolic (SBV (Interp tp))
atomToSymVar (Atom s (TIntRepr)) = free s 
atomToSymVar (Atom s (TBoolRepr)) = free s 
-- atomToSymVar (Atom s tr) = fail  $ "unknown atom type: " ++ (show tr)

mkEnv :: [Sampling] -> [(String, SomeExp)] -> Symbolic (Map.Map String SomeSBV)
mkEnv samps lets = do
    samplpairs <- forM samps $ \(Sampling distr x args) -> do
        let tr = typeOf distr
        sv <- atomToSymVar $ Atom x tr
        return $ (x, SomeSBV tr sv)
    let samplmap = Map.fromList samplpairs
        env = foldl (\aenv (x, (SomeExp tr e)) -> Map.insert x (SomeSBV tr (evalExpr aenv e)) aenv) samplmap lets
    return env




leafSatisfiable :: Leaf ret -> IO Bool
leafSatisfiable (Leaf samps lets conds ret) = do
    runSMT $ do
        env <- mkEnv samps lets
        constrain $ bAnd $ map (evalExpr env) conds
        query $ do
            cs <- checkSat
            case cs of
              Sat -> return True
              Unsat -> return False
              Unk -> fail "unknown"


