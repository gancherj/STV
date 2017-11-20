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

leafSatisfiable :: Leaf ret -> IO Bool
leafSatisfiable = error "unimp"

leavesEquiv :: [Leaf ret] -> [Leaf ret] -> IO Bool
leavesEquiv = error "unimp"


{-

   TODO finish. base types are SMT types, contexts are contexts

type family Interp (tp :: BaseType) :: * where
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

exprsEquiv :: Map.Map String SomeSBV -> [Expr tp] -> [Expr tp] -> IO Bool
exprsEquiv emap l1 l2 =
    case (length l1 == length l2) of
      True -> do
          bools <- mapM (\(p1,p2) -> exprEquiv emap p1 p2) (zip l1 l2)
          return $ bAnd bools
      False -> return False


someExpEquiv :: Map.Map String SomeSBV -> SomeExp -> SomeExp -> IO Bool
someExpEquiv env (SomeExp tr e1) (SomeExp tr' e2) =
    case (testEquality tr tr') of
      Just Refl -> exprEquiv env e1 e2
      Nothing -> return False


-- we do case analysis here to not require SymWord on tp
atomToSymVar :: Atom tp -> Symbolic (SBV (Interp tp))
atomToSymVar (Atom s (TIntRepr)) = free_ 
atomToSymVar (Atom s (TBoolRepr)) = free_ 
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
leafCondsEquiv l1 l2 = 
    case (unifyLeaves l1 l2) of
      Just ((Leaf samps1 conds1 ret1), (Leaf samps2 conds2 ret2)) -> do
        runSMT $ do
            env <- mkEnv samps1
            let phi1 = bAnd $ map (evalExpr env) conds1
                phi2 = bAnd $ map (evalExpr env) conds2
            constrain $ bnot (phi1 <=> phi2)
            query $ do
                cs <- checkSat
                case cs of 
                  Sat -> return False
                  Unsat -> return True
                  Unk -> fail "unknown"
      Nothing -> return False

-- unifyLeaves takes two leaves, and unifies their names so that they can be compared by the SMT solver. Returns Nothing if they cannot be unified.
unifyLeaves :: Leaf ret -> Leaf ret -> Maybe (Leaf ret, Leaf ret)
unifyLeaves (Leaf samps1 conds1 ret1) (Leaf samps2 conds2 ret2) = do
    emap <- unifySamps samps1 samps2
    let newsamps2 = map (\(Sampling d s args) -> Sampling d s (map (someExprSub emap) args)) samps2
        newconds2 = map (exprSub emap) conds2
        newret2 = exprSub emap ret2
    return $ ((Leaf samps1 conds1 ret1), (Leaf newsamps2 newconds2 newret2))

-- unifysamps takes two samplings, and returns a map of substitutions to unify the second sampling with the first. if this can't be done it returns Nothing
unifySamps :: [Sampling] -> [Sampling] -> Maybe (Map.Map String SomeExp)
unifySamps = error "unimp"

argsEquiv :: Map.Map String SomeSBV -> [SomeExp] -> [SomeExp] -> IO Bool
argsEquiv emap args1 args2 =
    case (length args1 == length args2) of
      True -> do
          let argpairs = zip args1 args2
          bools <- mapM (\(p1, p2) -> someExpEquiv emap p1 p2) argpairs
          return $ bAnd bools
      False -> return False

-- given a map so far of subs from right samplings to lefts, determine if the next sampling is equivalent. this is true when the args are equivalent, the distr name is the same, and the distr conds are equivalent.
equivSampl :: Map.Map String SomeExp -> Map.Map String SomeSBV -> Sampling -> Sampling -> IO Bool
equivSampl submap emap (Sampling distr1 x1 args1) (Sampling distr2 x2 args2) = do
    argsequiv <- argsEquiv emap args1 (map (someExprSub submap) args2)
    case argsequiv of
      False -> return False
      True ->
          case (distr1, distr2) of
            (SymDistr dn tp conds, SymDistr dn' tp' conds') ->
                case (dn == dn', testEquality tp tp') of
                  (True, Just Refl) -> do
                      -- now test for equivalent conditions
                      let x = (mkAtom x1 tp)  
                          conds1 = conds x args1
                          conds2 = conds' x (map (someExprSub submap) args2)
                      exprsEquiv emap conds1 conds2
                  _ -> return False
            (UnifInt i1 i2, UnifInt i1' i2') -> return $ (i1 == i2) && (i1' == i2')
            (UnifBool, UnifBool) -> return True
            _ -> return False


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
-}

leavesEquiv :: [Leaf rtp] -> [Leaf rtp] -> IO Bool
leavesEquiv = fail "unimp"
-}
