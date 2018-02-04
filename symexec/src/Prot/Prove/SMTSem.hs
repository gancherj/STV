
module Prot.Prove.SMTSem (
    SInterp,
    SInterp',
    evalExpr,
    exprEquiv,
    genFree,
    someExpEquivUnder,
    someExprsEquivUnder,
    condSatisfiable,
    mkMap,
    mkMapForall,
    genFreeForall)
   
   where 

import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Analyze
import Prot.Lang.Types
import Data.SBV
import Data.SBV.Control
import Data.Type.Equality
import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Graph.Inductive.Query.Matchings as G
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.PatriciaTree as G
import Data.Parameterized.Ctx 
import Data.Parameterized.Classes 
import Data.Parameterized.Some 
import Data.Parameterized.NatRepr 
import Data.Parameterized.TraversableFC as F
import Data.Parameterized.TraversableF as F
import Control.Monad.Trans.Class
import Data.Functor.Identity
import qualified Data.Vector as V
--- SMT Interpretation of language



type family SInterp (tp :: Type) :: * where
    SInterp TUnit = ()
    SInterp TInt = SInteger
    SInterp (TNat _) = SInteger
    SInterp TBool = SBool
    SInterp (TList w tp) = V.Vector (SInterp' tp)
    SInterp (TTuple ctx) = Ctx.Assignment SInterp' ctx

data SInterp' tp = SI { unSI :: SInterp tp }

data SomeSInterp = forall tp. SomeSInterp (TypeRepr tp) (SInterp tp)

instance Show SomeSInterp where
    show (SomeSInterp TUnitRepr x) = "()"
    show (SomeSInterp TIntRepr x) = show x
    show (SomeSInterp TBoolRepr y) = show y
    show _ = "<tuple>"

data ZipInterp tp = ZipInterp (TypeRepr tp) (SInterp tp)
data ZipZip tp = ZipZip (ZipInterp tp) (ZipInterp tp)

instance EqSymbolic SomeSInterp where
    (.==) (SomeSInterp TUnitRepr a) (SomeSInterp TUnitRepr b) = true
    (.==) (SomeSInterp TIntRepr a) (SomeSInterp TIntRepr b) = a .== b
    (.==) (SomeSInterp TBoolRepr a) (SomeSInterp TBoolRepr b) = a .== b
    (.==) (SomeSInterp (TTupleRepr ctx) a) (SomeSInterp (TTupleRepr ctx') b) = 
        case (testEquality ctx ctx') of
          Just Refl ->
              let z1 = Ctx.zipWith (\x y -> ZipInterp x (unSI y)) ctx a
                  z2 = Ctx.zipWith (\x y -> ZipInterp x (unSI y)) ctx b
                  z = Ctx.zipWith (\x y -> ZipZip x y) z1 z2
                  sbools = F.toListFC (\(ZipZip (ZipInterp tp1 si1) (ZipInterp tp2 si2)) ->
                      case (testEquality tp1 tp2) of
                        Just Refl ->
                            (SomeSInterp tp1 si1) .== (SomeSInterp tp1 si2)
                        Nothing -> false) z in
              bAnd sbools
          Nothing -> false

    (.==) (SomeSInterp tr1 _) (SomeSInterp tr2 _) =
        case (testEquality tr1 tr2) of
          Just Refl -> error $ "unimplemented symbolic equality for " ++ (show tr1)
          Nothing -> false
--    (.==) _ _ = false

evalExpr :: Map.Map String (SomeSInterp) -> Expr tp -> Symbolic (SInterp tp)
evalExpr emap (AtomExpr (Atom x tr)) =
    case Map.lookup x emap of
      Just (SomeSInterp tr2 e) ->
          case testEquality tr tr2 of
            Just Refl -> return e
            _ -> error $ "type error: got " ++ (show tr2) ++ " but expected " ++ (show tr)
      _ -> error $ "not found: " ++ x ++ " in emap " ++ (show emap)

evalExpr emap (Expr (UnitLit)) = return ()
evalExpr emap (Expr (IntLit i)) = return $ literal i
evalExpr emap (Expr (IntAdd e1 e2)) = liftM2 (+) (evalExpr emap e1) (evalExpr emap e2)

evalExpr emap (Expr (IntMul e1 e2)) = liftM2 (*) (evalExpr emap e1) (evalExpr emap e2)
evalExpr emap (Expr (IntNeg e1 )) = do
    e <- evalExpr emap e1
    return $ -e

evalExpr emap (Expr (BoolLit b)) = return $ literal b
evalExpr emap (Expr (BoolAnd b1 b2)) = liftM2 (&&&) (evalExpr emap b1) (evalExpr emap b2)
evalExpr emap (Expr (BoolOr b1 b2)) = liftM2 (|||) (evalExpr emap b1) (evalExpr emap b2)
evalExpr emap (Expr (BoolXor b1 b2)) = liftM2 (<+>) (evalExpr emap b1) (evalExpr emap b2)
evalExpr emap (Expr (BoolNot e1 )) = bnot <$> (evalExpr emap e1) 

evalExpr emap (Expr (IntLe e1 e2)) = liftM2 (.<=) (evalExpr emap e1) (evalExpr emap e2)
evalExpr emap (Expr (IntLt e1 e2)) = liftM2 (.<) (evalExpr emap e1)  (evalExpr emap e2)
evalExpr emap (Expr (IntGt e1 e2)) = liftM2 (.>) (evalExpr emap e1) (evalExpr emap e2)
evalExpr emap (Expr (IntEq e1 e2)) = liftM2 (.==) (evalExpr emap e1) (evalExpr emap e2)
evalExpr emap (Expr (IntNeq e1 e2)) = liftM2 (./=) (evalExpr emap e1) (evalExpr emap e2)

evalExpr emap (Expr (MkTuple cr asgn)) = Ctx.traverseWithIndex (\i e -> SI <$> evalExpr emap e) asgn

evalExpr emap (Expr (TupleEq e1 e2)) = do
    x <- evalExpr emap e1
    y <- evalExpr emap e2
    return $ (SomeSInterp (typeOf e1) x) .== (SomeSInterp (typeOf e2) y)
    
evalExpr emap (Expr (TupleGet tup ind tp)) = do
    t <- evalExpr emap tup
    return $ unSI $ t Ctx.! ind
    
evalExpr emap (Expr (TupleSet tup ind e)) = do
    a <- evalExpr emap e
    b <- evalExpr emap tup
    return $ Ctx.update ind (SI a) b

evalExpr emap (Expr (NatLit i)) = return $ literal (natValue i)

evalExpr emap (Expr (ListBuild (l :: TypeRepr tp) w f)) = do
    let (es :: [Expr tp]) = natForEach (knownNat :: NatRepr 0) w f
    (vs :: [SInterp tp]) <- mapM (evalExpr emap) es
    return $ ((V.fromList (map SI vs)))

evalExpr emap (Expr (ListLen i)) = do
    v <- evalExpr emap i
    return $ literal $ fromIntegral $ V.length v

evalExpr emap (Expr (ListGetIndex l i)) = do
    v <- evalExpr emap l
    ans <- vectorIndex v i
    return (unSI ans)
   
evalExpr emap (Expr (ListSetIndex l i v)) = do
    vl <- evalExpr emap l
    vv <- evalExpr emap v
    vectorSet vl i (SI vv)


vectorIndex :: V.Vector a -> (Expr (TNat w)) -> Symbolic a
vectorIndex v i = 
    case i of
      Expr (NatLit w) ->
          return $ v V.! (fromInteger $ natValue w)
      _ ->  
        error "need to do binary branching etc"

vectorSet :: V.Vector a -> Expr (TNat w) -> a -> Symbolic (V.Vector a)
vectorSet l i a = 
    case i of
      Expr (NatLit w) ->
          return $ l V.// [(fromInteger $ natValue w, a)]
      _ -> 
          error "need to do binary branching etc"

exprEquiv :: [Sampling] -> Expr tp -> Expr tp -> IO Bool
exprEquiv env e1 e2 = exprEquivUnder env [] e1 e2

exprEquivUnder :: [Sampling] -> [Expr TBool] -> Expr tp -> Expr tp -> IO Bool
exprEquivUnder samps conds e1 e2 = do
    runSMT $ do
        env <- mkEnv samps
        ans1 <- evalExpr env e1
        ans2 <- evalExpr env e2
        constrain $ (SomeSInterp (typeOf e1) ans1) ./= (SomeSInterp (typeOf e2) ans2)
        forM_ conds $ \cond -> do
            bc <- evalExpr env cond
            constrain $ bc .== true
        query $ do
            cs <- checkSat
            case cs of
              Sat -> return False
              Unsat -> return True
              Unk -> fail "unknown"

someExpEquivUnder :: [Sampling] -> [Expr TBool] -> SomeExp -> SomeExp -> IO Bool
someExpEquivUnder emap conds (SomeExp t1 e1) (SomeExp t2 e2) =
    case testEquality t1 t2 of
      Just Refl -> exprEquivUnder emap conds e1 e2
      Nothing -> return False

someExprsEquivUnder :: [Sampling] -> [Expr TBool] -> [SomeExp] -> [SomeExp] -> IO Bool
someExprsEquivUnder emap conds l1 l2 | length l1 /= length l2 = return False
  | otherwise = do
      bools <- mapM (\(e1,e2) -> someExpEquivUnder emap conds e1 e2) (zip l1 l2)
      return $ bAnd bools




-- we do case analysis here to not require SymWord on tp
atomToSymVar :: Atom tp -> Symbolic (SInterp tp)
atomToSymVar (Atom s tp) = genFree s tp
   
genFree :: String -> TypeRepr tp -> Symbolic (SInterp tp)
genFree s TUnitRepr = return ()
genFree s TIntRepr = free_
genFree s TBoolRepr = free_
genFree s (TTupleRepr ctx) = Ctx.traverseWithIndex (\i repr -> SI <$> genFree (s ++ (show i)) repr) ctx
genFree s (TListRepr w tp) = do
    ls <- sequence $ natForEach (knownNat :: NatRepr 0) w (\i -> SI <$> genFree (s ++ (show i)) tp)
    return $ V.fromList ls
genFree s (TNatRepr w) = do
    v <- free_
    constrain $ v .>= 0
    constrain $ v .<= (literal $ natValue w)
    return v

genFreeForall :: String -> TypeRepr tp -> Symbolic (SInterp tp)
genFreeForall s TUnitRepr = return ()
genFreeForall s TIntRepr = forall_
genFreeForall s TBoolRepr = forall_
genFreeForall s (TTupleRepr ctx) = Ctx.traverseWithIndex (\i repr -> SI <$> genFreeForall (s ++ (show i)) repr) ctx
genFreeForall s (TListRepr w tp) = do
    ls <- sequence $ natForEach (knownNat :: NatRepr 0) w (\i -> SI <$> genFreeForall (s ++ (show i)) tp)
    return $ V.fromList ls
genFreeForall s (TNatRepr w) = do
    v <- forall_
    constrain $ v .>= 0
    constrain $ v .<= (literal $ natValue w)
    return v

mkEnv :: [Sampling] -> Symbolic (Map.Map String SomeSInterp)
mkEnv samps = do
    samplpairs <- forM samps $ \(Sampling distr x args) -> do
        let tr = typeOf distr
        sv <- atomToSymVar $ Atom x tr
        return $ (x, SomeSInterp tr sv)
    return $ Map.fromList samplpairs

mkMap :: [(String, Some TypeRepr)] -> Symbolic (Map.Map String SomeSInterp)
mkMap ts = do
    samplpairs <- forM ts $ \(x, Some tp) -> do
        sv <- genFree x tp
        return $ (x, SomeSInterp tp sv)
    return $ Map.fromList samplpairs

mkMapForall :: [(String, Some TypeRepr)] -> Symbolic (Map.Map String SomeSInterp)
mkMapForall ts = do
    samplpairs <- forM ts $ \(x, Some tp) -> do
        sv <- genFreeForall x tp
        return $ (x, SomeSInterp tp sv)
    return $ Map.fromList samplpairs


condSatisfiable :: [Sampling] -> [Expr TBool] -> Expr TBool -> IO Int
condSatisfiable samps conds b = do
    bsat <- go samps conds b
    bnotsat <- go samps conds (Expr (BoolNot b))
    case (bsat,bnotsat) of
      (True, False) -> return 0
      (False, True) -> return 1
      (True, True) -> return 2
      (False, False) -> error "absurd"

    where
        go samps conds b = runSMT $ do
            env <- mkEnv samps 
            bs <- mapM (evalExpr env) conds
            bb <- evalExpr env b
            constrain $ bAnd bs
            constrain $ bb
            query $ do
                cs <- checkSat
                case cs of
                  Sat -> return True
                  Unsat -> return False
                  Unk -> fail "unknown"


