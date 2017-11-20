module Prot.Lang.Expr where
import Prot.Lang.Types
import Data.SBV
import Data.Type.Equality
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some
import Data.Parameterized.Classes
import Data.Parameterized.TraversableFC as F

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

    MkTuple :: !(CtxRepr ctx) -> !(Ctx.Assignment f ctx) -> App f (TTuple ctx)
    TupleGet :: !(f (TTuple ctx)) -> !(Ctx.Index ctx tp) -> !(TypeRepr tp) -> App f tp
    TupleSet :: !(CtxRepr ctx) -> !(f (TTuple ctx)) -> !(Ctx.Index ctx tp) -> !(f tp) -> App f (TTuple ctx)



data Expr tp = Expr !(App Expr tp) | AtomExpr !(Atom tp)

class IsExpr a where

instance IsExpr (Expr TInt) where

instance IsExpr (Expr TBool) where

instance IsExpr (Expr (TTuple ctx)) where


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
    typeOf (Expr (IntLe _ _)) = TBoolRepr
    typeOf (Expr (IntLt _ _)) = TBoolRepr
    typeOf (Expr (IntGt _ _)) = TBoolRepr
    typeOf (Expr (IntEq _ _)) = TBoolRepr
    typeOf (Expr (IntNeq _ _)) = TBoolRepr
    typeOf (Expr (MkTuple cr asgn)) = TTupleRepr cr
    typeOf (Expr (TupleGet cr ind tp)) = tp
    typeOf (Expr (TupleSet cr _ _ _)) = TTupleRepr cr



instance ShowF Expr where

instance Show (Expr tp) where
    show = ppExpr

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

ppExpr (Expr (MkTuple cr asgn)) = show asgn
ppExpr (Expr (TupleGet ag ind tp)) = (ppExpr ag) ++ "[" ++ (show ind) ++ "]"
ppExpr (Expr (TupleSet cr ag ind val)) = (ppExpr ag) ++ "{" ++ (show ind) ++ " -> " ++ (ppExpr val) ++ "}"

--- utility functions

exprsToCtx :: [SomeExp] -> (forall ctx. CtxRepr ctx -> Ctx.Assignment Expr ctx -> a) -> a
exprsToCtx es =
    go Ctx.empty Ctx.empty es
        where go :: CtxRepr ctx -> Ctx.Assignment Expr ctx -> [SomeExp] -> (forall ctx'. CtxRepr ctx' -> Ctx.Assignment Expr ctx' -> a) -> a
              go ctx asgn [] k = k ctx asgn
              go ctx asgn ((SomeExp tr e):vs) k = go (ctx Ctx.%> tr) (asgn Ctx.%> e) vs k

mkTuple :: [SomeExp] -> SomeExp
mkTuple es = exprsToCtx es $ \ctx asgn ->
    SomeExp (TTupleRepr ctx) (Expr (MkTuple ctx asgn))

getIth :: SomeExp -> Int -> SomeExp
getIth (SomeExp (TTupleRepr ctx) e) i 
 | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) =
     let tpr = ctx Ctx.! idx in
         SomeExp tpr (Expr (TupleGet e idx tpr))
getIth _ _ = error "bad getIth"


setIth :: SomeExp -> Int -> SomeExp -> SomeExp
setIth (SomeExp (TTupleRepr ctx) e) i (SomeExp stp s) 
 | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) =
     let tpr = ctx Ctx.! idx in
     case (testEquality tpr stp) of
       Just Refl ->
           SomeExp (TTupleRepr ctx) (Expr (TupleSet ctx e idx s))
       Nothing -> error "type error in set"
setIth _ _ _ = error "bad setIth"

getTupleElems :: SomeExp -> [SomeExp]
getTupleElems e@(SomeExp (TTupleRepr ctx) _) =
    let s = Ctx.sizeInt (Ctx.size ctx) in
    map (getIth e) [0..(s-1)]

getTupleElems _ = error "bad getTupleElems"

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


instance Boolean (Expr TBool) where
    true = Expr (BoolLit True)
    false = Expr (BoolLit False)
    bnot e = Expr (BoolNot e)
    (&&&) e1 e2 = Expr (BoolAnd e1 e2)
    (|||) e1 e2 = Expr (BoolOr e1 e2)



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

          go emap (Expr (MkTuple cr asgn)) = Expr (MkTuple cr (F.fmapFC (go emap) asgn))
          go emap (Expr (TupleGet tup ind etp)) = Expr (TupleGet (go emap tup) ind etp)
          go emap (Expr (TupleSet ctx tup ind e)) = Expr (TupleSet ctx (go emap tup) ind (go emap e))

someExprSub :: Map.Map String SomeExp -> SomeExp -> SomeExp
someExprSub emap e1 = 
    case e1 of
      (SomeExp tp e) ->
          SomeExp tp (exprSub emap e)

class FreeVar a where
    freeVars :: a -> [String]

instance FreeVar (Expr tp) where

    freeVars (AtomExpr (Atom x tp)) = [x]
    freeVars (Expr (IntLit _)) = []
    freeVars (Expr (IntAdd e1 e2)) = (freeVars e1) ++ (freeVars e2)
    freeVars (Expr (IntMul e1 e2)) = (freeVars e1) ++ (freeVars e2)
    freeVars (Expr (IntNeg e1 )) = (freeVars e1) 

    freeVars (Expr (BoolLit _)) = []
    freeVars (Expr (BoolAnd e1 e2)) = (freeVars e1) ++ (freeVars e2)
    freeVars (Expr (BoolOr e1 e2)) = (freeVars e1) ++ (freeVars e2)
    freeVars (Expr (BoolXor e1 e2)) = (freeVars e1) ++ (freeVars e2)
    freeVars (Expr (BoolNot e1 )) = (freeVars e1) 

    freeVars (Expr (IntLe e1 e2)) = (freeVars e1) ++ (freeVars e2)
    freeVars (Expr (IntLt e1 e2)) = (freeVars e1) ++ (freeVars e2)
    freeVars (Expr (IntGt e1 e2)) = (freeVars e1) ++ (freeVars e2)
    freeVars (Expr (IntEq e1 e2)) = (freeVars e1) ++ (freeVars e2)
    freeVars (Expr (IntNeq e1 e2)) = (freeVars e1) ++ (freeVars e2)

    freeVars (Expr (MkTuple _ asgn)) = concat $ toListFC freeVars asgn
    freeVars (Expr (TupleGet tup _ _)) = freeVars tup
    freeVars (Expr (TupleSet _ tup _ e)) = (freeVars tup) ++ (freeVars e)

instance FreeVar SomeExp where
    freeVars (SomeExp tp e) = freeVars e
