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
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Ctx 
import Data.Parameterized.Classes 
import Data.Parameterized.Some 
import Data.Parameterized.TraversableFC as F
import Data.Parameterized.TraversableF as F



leavesEquiv :: [Leaf ret] -> [Leaf ret] -> IO Bool
leavesEquiv = fail "unimp" -- TODO


type family SInterp (tp :: Type) :: * where
    SInterp TInt = SInteger
    SInterp TBool = SBool
    SInterp (TTuple ctx) = Ctx.Assignment SInterp' ctx


data SInterp' tp = SI { unSI :: SInterp tp }

data SomeSInterp = forall tp. SomeSInterp (TypeRepr tp) (SInterp tp)

data ZipInterp tp = ZipInterp (TypeRepr tp) (SInterp tp)
data ZipZip tp = ZipZip (ZipInterp tp) (ZipInterp tp)

instance EqSymbolic SomeSInterp where
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
                            case tp1 of
                              TIntRepr -> si1 .== si2
                              TBoolRepr -> si1 .== si2
                              TTupleRepr ictx -> (SomeSInterp tp1 si1) .== (SomeSInterp tp1 si2) 
                        Nothing -> false)  z in
                  bAnd sbools
          Nothing -> false
    (.==) _ _ = false

evalExpr :: Map.Map String (SomeSInterp) -> Expr tp -> SInterp tp
evalExpr emap (AtomExpr (Atom x tr)) =
    case Map.lookup x emap of
      Just (SomeSInterp tr2 e) ->
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

evalExpr emap (Expr (MkTuple cr asgn)) = F.fmapFC (SI . (evalExpr emap)) asgn
evalExpr emap (Expr (TupleGet tup ind tp)) = unSI $ (evalExpr emap tup) Ctx.! ind
evalExpr emap (Expr (TupleSet cr tup ind e)) = 
    Ctx.update ind (SI $ evalExpr emap e) (evalExpr emap tup)


exprEquiv :: Map.Map String SomeSInterp -> Expr tp -> Expr tp -> IO Bool
exprEquiv env e1 e2 = 
    runSMT $ do
        constrain $ (SomeSInterp (typeOf e1) (evalExpr env e1)) ./= (SomeSInterp (typeOf e2) (evalExpr env e2))
        query $ do
            cs <- checkSat
            case cs of
              Sat -> return False
              Unsat -> return True
              Unk -> fail "unknown"


exprsEquiv :: Map.Map String SomeSInterp -> [Expr tp] -> [Expr tp] -> IO Bool
exprsEquiv emap l1 l2 =
    case (length l1 == length l2) of
      True -> do
          bools <- mapM (\(p1,p2) -> exprEquiv emap p1 p2) (zip l1 l2)
          return $ bAnd bools
      False -> return False


someExpEquiv :: Map.Map String SomeSInterp -> SomeExp -> SomeExp -> IO Bool
someExpEquiv env (SomeExp tr e1) (SomeExp tr' e2) =
    case (testEquality tr tr') of
      Just Refl -> exprEquiv env e1 e2
      Nothing -> return False

-- we do case analysis here to not require SymWord on tp
atomToSymVar :: Atom tp -> Symbolic (SInterp tp)
atomToSymVar (Atom s tp) = go s tp
    where go :: String -> TypeRepr tp -> Symbolic (SInterp tp)
          go s TIntRepr = free_
          go s TBoolRepr = free_
          go s (TTupleRepr ctx) = fail "unimp" -- TODO

-- atomToSymVar (Atom s tr) = fail  $ "unknown atom type: " ++ (show tr)



mkEnv :: [Sampling] -> Symbolic (Map.Map String SomeSInterp)
mkEnv samps = do
    samplpairs <- forM samps $ \(Sampling distr x args) -> do
        let tr = typeOf distr
        sv <- atomToSymVar $ Atom x tr
        return $ (x, SomeSInterp tr sv)
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


-- TODO rest
