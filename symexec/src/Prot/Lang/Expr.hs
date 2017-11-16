module Prot.Lang.Expr where
import Prot.Lang.Types

data App (f :: Type -> *) (tp :: Type) where
    IntLit :: !Int -> App f TInt
    IntAdd :: !(f TInt) -> !(f TInt) -> App f TInt
    IntMul :: !(f TInt) -> !(f TInt) -> App f TInt
    IntNeg :: !(f TInt) -> App f TInt

    BoolLit :: !Bool -> App f TBool
    BoolAnd :: !(f TBool) -> !(f TBool) -> App f TBool
    BoolOr :: !(f TBool) -> !(f TBool) -> App f TBool
    BoolXor :: !(f TBool) -> !(f TBool) -> App f TBool
    BoolNot :: !(f TBool) -> App f TBool

    -- TODO tuples using CtxReprs

data Expr tp = Expr !(App Expr tp) | AtomExpr !(Atom tp)

typeOf :: Expr tp -> TypeRepr tp
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


