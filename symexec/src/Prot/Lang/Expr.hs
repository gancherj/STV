module Prot.Lang.Expr where
import Prot.Lang.Types
import Data.SBV
import Data.Type.Equality
import qualified Data.Map.Strict as Map

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

---
-- instances

instance Num (Expr TInt) where
    e1 + e2 = Expr (IntAdd e1 e2)
    e1 * e2 = Expr (IntMul e1 e2)
    signum e = error "signum unimp"
    abs e = error "abs unimp"
    fromInteger i = Expr (IntLit i)
    negate e = Expr (IntNeg e)

(|<|) :: Expr TInt -> Expr TInt -> Expr TBool
e1 |<| e2 = Expr (IntLt e1 e2)

(|>|) :: Expr TInt -> Expr TInt -> Expr TBool
e1 |>| e2 = Expr (IntGt e1 e2)

(|<=|) :: Expr TInt -> Expr TInt -> Expr TBool
e1 |<=| e2 = Expr (IntLe e1 e2)


--- expr utility functions
 --

-- perform substitutions according to map. guarantees result expr is free of names in substitutions.
--
runFor :: Int -> (a -> a) -> a -> a
runFor 0 f a = a
runFor i f a = runFor (i - 1) f (f a)

exprSub :: Map.Map String SomeExp -> Expr tp -> Expr tp
exprSub emap e = runFor (Map.size emap) (go emap) e
    where go :: Map.Map String SomeExp -> Expr tp -> Expr tp
          go emap (AtomExpr (Atom x tp)) =
              case (Map.lookup x emap) of
                Just (SomeExp tp2 e) ->
                    case (testEquality tp tp2) of
                      Just Refl -> e
                      Nothing -> error "type error"
                Nothing -> error "var not found"
          go emap (Expr (IntLit i)) = Expr (IntLit i)
          go emap (Expr (IntAdd e1 e2)) = Expr (IntAdd (go emap e1) (go emap e2))
          go emap (Expr (IntMul e1 e2)) = Expr (IntMul (go emap e1) (go emap e2))
          go emap (Expr (IntNeg e1)) = Expr (IntNeg (go emap e1))

          go emap (Expr (BoolLit b)) = Expr (BoolLit b)
          go emap (Expr (BoolAnd e1 e2)) = Expr (BoolAnd (go emap e1) (go emap e2))
          go emap (Expr (BoolOr e1 e2)) = Expr (BoolOr (go emap e1) (go emap e2))
          go emap (Expr (BoolXor e1 e2)) = Expr (BoolXor (go emap e1) (go emap e2))
          go emap (Expr (BoolNot e1 )) = Expr (BoolNot (go emap e1))
    
          go emap (Expr (IntLe e1 e2)) = Expr (IntLe (go emap e1) (go emap e2))
          go emap (Expr (IntLt e1 e2)) = Expr (IntLt (go emap e1) (go emap e2))
          go emap (Expr (IntGt e1 e2)) = Expr (IntGt (go emap e1) (go emap e2))
          go emap (Expr (IntEq e1 e2)) = Expr (IntEq (go emap e1) (go emap e2))
          go emap (Expr (IntNeq e1 e2)) = Expr (IntNeq (go emap e1) (go emap e2))

someExprSub :: Map.Map String SomeExp -> SomeExp -> SomeExp
someExprSub emap e1 = 
    case e1 of
      (SomeExp tp e) ->
          SomeExp tp (exprSub emap e)


