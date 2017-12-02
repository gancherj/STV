module Prot.Lang.Run where
import Prot.Lang.Command
import Prot.Lang.Expr
import Prot.Lang.Types
import Data.Type.Equality

import Data.Parameterized.TraversableFC as F
import Data.Parameterized.TraversableF as F
import Data.Parameterized.Pair as P
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import Data.Parameterized.Some
import qualified Data.Map.Strict as Map


type family TInterp (tp :: Type) :: * where
    TInterp TInt = Integer
    TInterp TBool = Bool
    TInterp (TTuple ctx) = Ctx.Assignment TInterp' ctx
    TInterp (TEnum t) = TypeableValue t


newtype TInterp' tp = TI {unTI :: TInterp tp}

data SomeInterp = forall tp. SomeInterp (TypeRepr tp) (TInterp tp)

instance Show SomeInterp where
    show (SomeInterp TIntRepr ti) = (show ti)
    show (SomeInterp TBoolRepr ti) = (show ti)
    show (SomeInterp (TTupleRepr ctx) ti) = showTupleInterp ctx ti
    show (SomeInterp (TEnumRepr tp) ti) = (show ti)

data PPInterp tp = PPInterp (TypeRepr tp) (TInterp tp)

showTupleInterp :: CtxRepr ctx -> Ctx.Assignment TInterp' ctx -> String
showTupleInterp ctx asgn = 
    let z = Ctx.zipWith (\a b -> PPInterp a (unTI b)) ctx asgn 
        valstrs = F.toListFC (\(PPInterp tr val) ->
            case tr of
              TIntRepr -> show val
              TBoolRepr -> show val
              TEnumRepr tp -> show val
              TTupleRepr ictx -> showTupleInterp ictx val
              ) z in
    "[" ++ (concatMap (\s -> s ++ ", ") valstrs) ++ "]"


evalExpr :: Map.Map String (SomeInterp) -> Expr tp -> TInterp tp
evalExpr emap (AtomExpr (Atom x tr)) = 
    case Map.lookup x emap of
      Just (SomeInterp tr2 e) ->
          case testEquality tr tr2 of
            Just Refl -> e
            _ -> error "type error"
      _ -> error "not found"

evalExpr emap (Expr (IntLit i)) = i
evalExpr emap (Expr (IntAdd e1 e2)) = (evalExpr emap e1) + (evalExpr emap e2)
evalExpr emap (Expr (IntMul e1 e2)) = (evalExpr emap e1) * (evalExpr emap e2)
evalExpr emap (Expr (IntNeg e1 )) = -(evalExpr emap e1) 

evalExpr emap (Expr (BoolLit b)) = b
evalExpr emap (Expr (BoolAnd b1 b2)) = (evalExpr emap b1) && (evalExpr emap b2)
evalExpr emap (Expr (BoolOr b1 b2)) = (evalExpr emap b1) || (evalExpr emap b2)
evalExpr emap (Expr (BoolXor b1 b2)) = not $ (evalExpr emap b1) == (evalExpr emap b2)
evalExpr emap (Expr (BoolNot e1 )) = not (evalExpr emap e1) 

evalExpr emap (Expr (IntLe e1 e2)) = (evalExpr emap e1) <= (evalExpr emap e2)
evalExpr emap (Expr (IntLt e1 e2)) = (evalExpr emap e1) < (evalExpr emap e2)
evalExpr emap (Expr (IntGt e1 e2)) = (evalExpr emap e1) > (evalExpr emap e2)
evalExpr emap (Expr (IntEq e1 e2)) = (evalExpr emap e1) == (evalExpr emap e2)
evalExpr emap (Expr (IntNeq e1 e2)) = not $ (evalExpr emap e1) == (evalExpr emap e2)

evalExpr emap (Expr (MkTuple cr asgn)) = F.fmapFC (TI . (evalExpr emap)) asgn
evalExpr emap (Expr (TupleGet cr tup ind tp)) = unTI $ (evalExpr emap tup) Ctx.! ind
evalExpr emap (Expr (TupleSet cr tup ind e)) = 
    Ctx.update ind (TI $ evalExpr emap e) (evalExpr emap tup)

evalExpr emap (Expr (EnumLit _)) = error "enum dont care"
evalExpr emap (Expr (EnumEq _ _ _)) = error "enum dont care"


runQuery :: String -> String -> TypeRepr tp -> IO (TInterp tp)
runQuery x dn TIntRepr = do
    putStrLn $ x ++ " <- " ++ dn ++ ":"
    line <- getLine
    return $ read line
runQuery x dn TBoolRepr = do
    putStrLn $ x ++ " <- " ++ dn ++ ":"
    line <- getLine
    return $ read line
runQuery x dn (TTupleRepr ctxrepr) = do
    asgn <- Ctx.traverseWithIndex (\i repr -> do
        e <- runQuery (x ++ "[" ++ (show (Ctx.indexVal i)) ++ "]") dn repr
        return $ TI e) ctxrepr
    return $ asgn
runQuery x dn (TEnumRepr t) = fail "enum query"


runCommand_ :: Map.Map String (SomeInterp) -> Command tp -> IO (TInterp tp)
runCommand_ emap (Sampl x (SymDistr dn tr dconds) ls k) = do
    a <- runQuery x dn tr
    let newmap = Map.insert x (SomeInterp tr a) emap
    runCommand_ newmap k
runCommand_ emap (Sampl x (UnifInt _ _) ls k) = do
    a <- runQuery x "unif" TIntRepr
    let newmap = Map.insert x (SomeInterp TIntRepr a) emap
    runCommand_ newmap k
runCommand_ emap (Sampl x (UnifBool) ls k) = do
    a <- runQuery x "unif" TBoolRepr
    let newmap = Map.insert x (SomeInterp TBoolRepr a) emap
    runCommand_ newmap k

runCommand_ emap (Let x e k) = runCommand_ (Map.insert x (SomeInterp (typeOf e) (evalExpr emap e)) emap) k
runCommand_ emap (Ite b c1 c2) = case (evalExpr emap b) of
                                   True -> runCommand_ emap c1
                                   False -> runCommand_ emap c2
runCommand_ emap (Ret e) = return $ evalExpr emap e

runCommand :: Command tp -> IO (TInterp tp)
runCommand = runCommand_ (Map.empty)
    
