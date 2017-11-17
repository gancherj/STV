module Prot.Lang.Run where
import Prot.Lang.Command
import Prot.Lang.Expr
import Prot.Lang.Types
import Data.Type.Equality

import Data.Map.Strict as Map


type family TInterp (tp :: Type) :: * where
    TInterp TInt = Integer
    TInterp TBool = Bool

data SomeInterp = forall tp. SomeInterp (TypeRepr tp) (TInterp tp)

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

runCommand_ :: Map.Map String (SomeInterp) -> Command tp -> IO (TInterp tp)
runCommand_ emap (Sampl x (SymDistr dn TIntRepr dconds) ls k) = do
    putStrLn $ x ++ " <- " ++ dn ++ ":"
    line <- getLine
    runCommand_ (Map.insert x (SomeInterp TIntRepr (read line)) emap) k
runCommand_ emap (Sampl x (SymDistr dn TBoolRepr dcs) ls k) = do
    putStr $ x ++ " <- " ++ dn ++ ":"
    line <- getLine
    runCommand_ (Map.insert x (SomeInterp TBoolRepr (read line)) emap) k

runCommand_ emap (Let x e k) = runCommand_ (Map.insert x (SomeInterp (typeOf e) (evalExpr emap e)) emap) k
runCommand_ emap (Ite b c1 c2) = case (evalExpr emap b) of
                                   True -> runCommand_ emap c1
                                   False -> runCommand_ emap c2
runCommand_ emap (Ret e) = return $ evalExpr emap e

runCommand :: Command tp -> IO (TInterp tp)
runCommand = runCommand_ (Map.empty)
    
