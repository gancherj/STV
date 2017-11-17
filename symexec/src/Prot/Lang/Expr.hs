module Prot.Lang.Expr where
import Prot.Lang.Types

class TypeOf (k :: Type -> *) where
    typeOf :: forall tp. k tp -> TypeRepr tp

data App (f :: Type -> *) (tp :: Type) where
    IntLit :: !Integer -> App f TInt
    IntAdd :: !(f TInt) -> !(f TInt) -> App f TInt
    IntMul :: !(f TInt) -> !(f TInt) -> App f TInt
    IntNeg :: !(f TInt) -> App f TInt

    BoolLit :: !Bool -> App f TBool
    BoolAnd :: !(f TBool) -> !(f TBool) -> App f TBool
    BoolOr :: !(f TBool) -> !(f TBool) -> App f TBool
    BoolXor :: !(f TBool) -> !(f TBool) -> App f TBool
    BoolNot :: !(f TBool) -> App f TBool

    IntLe :: !(f TInt) -> !(f TInt) -> App f TBool
    IntLt :: !(f TInt) -> !(f TInt) -> App f TBool
    IntGt :: !(f TInt) -> !(f TInt) -> App f TBool
    IntEq :: !(f TInt) -> !(f TInt) -> App f TBool
    IntNeq :: !(f TInt) -> !(f TInt) -> App f TBool



data Expr tp = Expr !(App Expr tp) | AtomExpr !(Atom tp)

instance TypeOf Expr where

    typeOf (AtomExpr (Atom _ t)) = t
    typeOf (Expr (IntLit _)) = TIntRepr
    typeOf (Expr (IntAdd _ _)) = TIntRepr
    typeOf (Expr (IntMul _ _)) = TIntRepr
    typeOf (Expr (IntNeg _)) = TIntRepr
    typeOf (Expr (BoolLit _)) = TBoolRepr
    typeOf (Expr (BoolNot _)) = TBoolRepr
    typeOf (Expr (BoolAnd _ _)) = TBoolRepr
    typeOf (Expr (BoolOr _ _)) = TBoolRepr
    typeOf (Expr (BoolXor _ _)) = TBoolRepr




data Atom tp = Atom { atomName :: String, atomTypeRepr :: TypeRepr tp }

mkAtom :: String -> TypeRepr tp -> Expr tp
mkAtom s tr = AtomExpr $ Atom s tr

data SomeExp = forall tp. SomeExp (TypeRepr tp) (Expr tp)

ppSomeExp :: SomeExp -> String
ppSomeExp (SomeExp _ e) = ppExpr e

mkSomeExp :: Expr tp -> SomeExp
mkSomeExp e = SomeExp (typeOf e) e

ppExpr :: Expr tp -> String
ppExpr (AtomExpr (Atom x _)) = x
ppExpr (Expr (IntLit i)) = show i
ppExpr (Expr (IntAdd e1 e2)) = (ppExpr e1) ++ " + " ++ (ppExpr e2)
ppExpr (Expr (IntMul e1 e2)) = (ppExpr e1) ++ " * " ++ (ppExpr e2)
ppExpr (Expr (IntNeg e1)) = "-" ++ (ppExpr e1) 

ppExpr (Expr (BoolLit e1)) = show e1
ppExpr (Expr (BoolAnd e1 e2)) = (ppExpr e1) ++ " /\\ " ++ (ppExpr e2)
ppExpr (Expr (BoolOr e1 e2)) = (ppExpr e1) ++ " \\/ " ++ (ppExpr e2)
ppExpr (Expr (BoolXor e1 e2)) = (ppExpr e1) ++ " + " ++ (ppExpr e2)
ppExpr (Expr (BoolNot e1 )) = "not " ++ (ppExpr e1) 

ppExpr (Expr (IntLe e1 e2)) = (ppExpr e1) ++ " <= " ++ (ppExpr e2)
ppExpr (Expr (IntLt e1 e2)) = (ppExpr e1) ++ " < " ++ (ppExpr e2)
ppExpr (Expr (IntGt e1 e2)) = (ppExpr e1) ++ " >= " ++ (ppExpr e2)
ppExpr (Expr (IntEq e1 e2)) = (ppExpr e1) ++ " == " ++ (ppExpr e2)
ppExpr (Expr (IntNeq e1 e2)) = (ppExpr e1) ++ " != " ++ (ppExpr e2)
