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

data Expr tp = Expr !(App Expr tp) | AtomExpr !(Atom tp)

data Atom tp = Atom { atomName :: String, atomTypeRepr :: TypeRepr tp }

mkAtom :: String -> TypeRepr tp -> Expr tp
mkAtom s tr = AtomExpr $ Atom s tr

data SomeExp = forall tp. SomeExp (TypeRepr tp) (Expr tp)


