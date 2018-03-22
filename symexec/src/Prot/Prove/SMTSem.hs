
module Prot.Prove.SMTSem (
    SInterp,
    SInterp',
    SomeSInterp(SomeSInterp),
    Quant(Forall,Exists),
    evalExpr,
    evalSomeExpr,
    genSem,
    condSatisfiable,
    mkEnv,
    mkSamplEnv)
   
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

evalSomeExpr :: Map.Map String SomeSInterp -> SomeExp -> SomeSInterp
evalSomeExpr emap (SomeExp t e) = SomeSInterp t (evalExpr emap e)

evalExpr :: Map.Map String (SomeSInterp) -> Expr tp -> (SInterp tp)
evalExpr emap (AtomExpr (Atom x tr)) =
    case Map.lookup x emap of
      Just (SomeSInterp tr2 e) ->
          case testEquality tr tr2 of
            Just Refl -> e
            _ -> error $ "type error: got " ++ (show tr2) ++ " but expected " ++ (show tr)
      _ -> error $ "not found: " ++ x ++ " in emap " ++ (show emap)

evalExpr emap (Expr (UnitLit)) = ()
evalExpr emap (Expr (IntLit i)) = literal i
evalExpr emap (Expr (IntAdd e1 e2)) = (+) (evalExpr emap e1) (evalExpr emap e2)

evalExpr emap (Expr (IntMul e1 e2)) = (*) (evalExpr emap e1) (evalExpr emap e2)
evalExpr emap (Expr (IntNeg e1 )) = - (evalExpr emap e1)

evalExpr emap (Expr (BoolLit b)) = literal b
evalExpr emap (Expr (BoolAnd b1 b2)) = (&&&) (evalExpr emap b1) (evalExpr emap b2)
evalExpr emap (Expr (BoolOr b1 b2)) = (|||) (evalExpr emap b1) (evalExpr emap b2)
evalExpr emap (Expr (BoolXor b1 b2)) = (<+>) (evalExpr emap b1) (evalExpr emap b2)
evalExpr emap (Expr (BoolNot e1 )) = bnot (evalExpr emap e1) 

evalExpr emap (Expr (IntLe e1 e2)) = (.<=) (evalExpr emap e1) (evalExpr emap e2)
evalExpr emap (Expr (IntLt e1 e2)) = (.<) (evalExpr emap e1)  (evalExpr emap e2)
evalExpr emap (Expr (IntGt e1 e2)) = (.>) (evalExpr emap e1) (evalExpr emap e2)
evalExpr emap (Expr (IntEq e1 e2)) = (.==) (evalExpr emap e1) (evalExpr emap e2)
evalExpr emap (Expr (IntNeq e1 e2)) = (./=) (evalExpr emap e1) (evalExpr emap e2)

evalExpr emap (Expr (MkTuple cr asgn)) = F.fmapFC (\e -> SI $ evalExpr emap e) asgn

evalExpr emap (Expr (TupleEq e1 e2)) = 
    let x = evalExpr emap e1
        y = evalExpr emap e2 in
    (SomeSInterp (typeOf e1) x) .== (SomeSInterp (typeOf e2) y)
    
evalExpr emap (Expr (TupleGet tup ind tp)) = 
    let t = evalExpr emap tup in
    unSI $ t Ctx.! ind
    
evalExpr emap (Expr (TupleSet tup ind e)) = 
    let a = evalExpr emap e
        b = evalExpr emap tup  in
    Ctx.update ind (SI a) b

evalExpr emap (Expr (NatLit i)) = literal (natValue i)

evalExpr emap (Expr (ListBuild (l :: TypeRepr tp) w f)) = 
    error "unimp"

evalExpr emap (Expr (ListLen i)) = 
    let v = evalExpr emap i in
    literal $ fromIntegral $ V.length v

evalExpr emap (Expr (ListGetIndex l i)) = 
    let v = evalExpr emap l
        ans = vectorIndex v i in
    (unSI ans)
   
evalExpr emap (Expr (ListSetIndex l i v)) = 
    let vl = evalExpr emap l
        vv = evalExpr emap v in
    vectorSet vl i (SI vv)


vectorIndex :: V.Vector a -> (Expr (TNat w)) -> a
vectorIndex v i = 
    case i of
      Expr (NatLit w) ->
          v V.! (fromInteger $ natValue w)
      _ ->  
        -- will require SBV semantic if-then-else
        error "need to do binary branching etc"

vectorSet :: V.Vector a -> Expr (TNat w) -> a -> (V.Vector a)
vectorSet l i a = 
    case i of
      Expr (NatLit w) ->
          l V.// [(fromInteger $ natValue w, a)]
      _ -> 
          error "need to do binary branching etc"


data Quant = Forall | Exists
   

genForall :: TypeRepr tp -> Symbolic (SInterp tp)
genForall  TUnitRepr = return ()
genForall  TIntRepr = forall_
genForall  TBoolRepr = forall_
genForall  (TTupleRepr ctx) = Ctx.traverseWithIndex (\i repr -> SI <$> genForall repr) ctx
genForall  (TListRepr w tp) = do
    ls <- sequence $ natForEach (knownNat :: NatRepr 0) w (\i -> SI <$> genForall tp)
    return $ V.fromList ls
genForall  (TNatRepr w) = do
    v <- forall_
    constrain $ v .>= 0
    constrain $ v .<= (literal $ natValue w)
    return v

genExists :: TypeRepr tp -> Symbolic (SInterp tp)
genExists  TUnitRepr = return ()
genExists  TIntRepr = exists_
genExists  TBoolRepr = exists_
genExists  (TTupleRepr ctx) = Ctx.traverseWithIndex (\i repr -> SI <$> genExists repr) ctx
genExists  (TListRepr w tp) = do
    ls <- sequence $ natForEach (knownNat :: NatRepr 0) w (\i -> SI <$> genExists tp)
    return $ V.fromList ls
genExists  (TNatRepr w) = do
    v <- exists_
    constrain $ v .>= 0
    constrain $ v .<= (literal $ natValue w)
    return v

genSem :: TypeRepr tp -> Quant -> Symbolic (SInterp tp)
genSem tp Forall = genForall tp
genSem tp Exists = genExists tp


mkEnv :: [(String, Some TypeRepr, Quant)] -> Symbolic (Map.Map String SomeSInterp)
mkEnv ts = do
    samplpairs <- forM ts $ \(x, Some tp, q) -> do
        sv <- genSem tp q
        return $ (x, SomeSInterp tp sv)
    return $ Map.fromList samplpairs

mkSamplEnv :: Bool -> [Sampling] -> Symbolic (Map.Map String SomeSInterp)
mkSamplEnv b samps = do
    let env = map (\(Sampling d x args) -> (x, Some (typeOf d), if b then Forall else Exists)) samps
    mkEnv env

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
        go :: [Sampling] -> [Expr TBool] -> Expr TBool -> IO Bool
        go samps conds b = runSMT $ do
            env <- mkSamplEnv False samps 
            let bs = map (evalExpr env) conds
            let bb = evalExpr env b
            constrain $ bAnd bs
            constrain $ bb
            query $ do
                cs <- checkSat
                case cs of
                  Sat -> return True
                  Unsat -> return False
                  Unk -> fail "unknown"


