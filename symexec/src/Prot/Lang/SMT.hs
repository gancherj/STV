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

exprEquiv :: Map.Map String SomeSBV -> Expr tp -> Expr tp -> IO Bool
exprEquiv env e1 e2 = 
    runSMT $ do
        constrain $ (evalExpr env e1) ./= (evalExpr env e2)
        query $ do
            cs <- checkSat
            case cs of
              Sat -> return False
              Unsat -> return True
              Unk -> fail "unknown"


-- we do case analysis here to not require SymWord on tp
atomToSymVar :: Atom tp -> Symbolic (SBV (Interp tp))
atomToSymVar (Atom s (TIntRepr)) = free s 
atomToSymVar (Atom s (TBoolRepr)) = free s 
-- atomToSymVar (Atom s tr) = fail  $ "unknown atom type: " ++ (show tr)

mkEnv :: [Sampling] -> Symbolic (Map.Map String SomeSBV)
mkEnv samps = do
    samplpairs <- forM samps $ \(Sampling distr x args) -> do
        let tr = typeOf distr
        sv <- atomToSymVar $ Atom x tr
        return $ (x, SomeSBV tr sv)
    return $ Map.fromList samplpairs

leafSatisfiable :: Leaf ret -> IO Bool
leafSatisfiable (Leaf samps conds ret) = do
    runSMT $ do
        env <- mkEnv samps 
        constrain $ bAnd $ map (evalExpr env) conds
        query $ do
            cs <- checkSat
            case cs of
              Sat -> return True
              Unsat -> return False
              Unk -> fail "unknown"

leafCondsEquiv :: Leaf ret -> Leaf ret -> IO Bool
leafCondsEquiv (Leaf samps1 conds1 ret1) (Leaf samps2 conds2 ret2) = do
    runSMT $ do
        env1 <- mkEnv samps1 
        env2 <- mkEnv samps2 
        let phi1 = bAnd $ map (evalExpr env1) conds1
            phi2 = bAnd $ map (evalExpr env2) conds2
        constrain $ bnot (phi1 <=> phi2)
        query $ do
            cs <- checkSat
            case cs of 
              Sat -> return False
              Unsat -> return True
              Unk -> fail "unknown"

{-
findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe (a, [a]))
findM f [] = Nothing
findM f (x:xs) = do
    b <- f x
    if b then return $ Just (x, xs) else do
        res <- findM f xs
        case res of
          Just (a, as) ->
              return $ Just (a, x:as)
          Nothing -> Nothing

equivSampl :: Map.Map String SomeExpr -> Sampling -> Sampling -> IO Bool
equivSampl (Sampling distr1 x1 args1) (Sampling distr2 x2 args2) =
    case (distr1, distr2) of
      (SymDistr dn tp conds, SymDistr dn' tp' conds') ->
          case (dn == dn', testEquality tp tp') of
            (True, Just Refl) ->
                exprEquiv 
-}
