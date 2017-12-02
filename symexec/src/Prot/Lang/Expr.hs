{-# LANGUAGE AllowAmbiguousTypes #-}
module Prot.Lang.Expr where
import Prot.Lang.Types
import Data.SBV
import Data.Type.Equality
import Data.Typeable
import Data.Type.Equality
import qualified Data.Data as Data
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some
import Data.Parameterized.Classes
import Data.Parameterized.TraversableFC as F
import qualified Data.Set as Set

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
    TupleGet :: !(CtxRepr ctx) -> !(f (TTuple ctx)) -> !(Ctx.Index ctx tp) -> !(TypeRepr tp) -> App f tp
    TupleSet :: !(CtxRepr ctx) -> !(f (TTuple ctx)) -> !(Ctx.Index ctx tp) -> !(f tp) -> App f (TTuple ctx)

    EnumLit :: !(TypeableValue a) -> App f (TEnum a)
    EnumEq :: !(TypeableType a) -> !(f (TEnum a)) -> !(f (TEnum a)) -> App f TBool

data Expr tp = Expr !(App Expr tp) | AtomExpr !(Atom tp)

instance SynEq Expr where
    synEq (Expr e1) (Expr e2) = synEq e1 e2
    synEq (AtomExpr (Atom x tp1)) (AtomExpr (Atom y tp2)) = 
        case testEquality tp1 tp2 of
          Just Refl -> x ==y
          Nothing -> False
    synEq _ _ = False

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
    typeOf (Expr (TupleGet _ cr ind tp)) = tp
    typeOf (Expr (TupleSet cr _ _ _)) = TTupleRepr cr
    typeOf (Expr (EnumLit x )) = TEnumRepr $ typeableTypeOfValue x 
    typeOf (Expr (EnumEq _ x _)) = TBoolRepr



instance ShowF Expr where

instance Show (Expr tp) where
    show = ppExpr

data Atom tp = Atom { atomName :: String, atomTypeRepr :: TypeRepr tp }

mkAtom :: String -> TypeRepr tp -> Expr tp
mkAtom s tr = AtomExpr $ Atom s tr

data SomeExp = forall tp. SomeExp (TypeRepr tp) (Expr tp)

instance Eq SomeExp where
    (==) (SomeExp t1 e1) (SomeExp t2 e2) =
        case testEquality t1 t2 of
          Just Refl -> synEq e1 e2
          Nothing -> False


ppSomeExp :: SomeExp -> String
ppSomeExp (SomeExp _ e) = ppExpr e

mkSome :: Expr tp -> SomeExp
mkSome e = SomeExp (Prot.Lang.Expr.typeOf e) e

unSome :: SomeExp -> (forall tp. TypeRepr tp -> Expr tp -> a) -> a
unSome e k =
    case e of
      (SomeExp tp e) -> k tp e

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
ppExpr (Expr (TupleGet _ ag ind tp)) = (ppExpr ag) ++ "[" ++ (show ind) ++ "]"
ppExpr (Expr (TupleSet cr ag ind val)) = (ppExpr ag) ++ "{" ++ (show ind) ++ " -> " ++ (ppExpr val) ++ "}"

ppExpr (Expr (EnumLit i)) = show i
ppExpr (Expr (EnumEq _ x y)) = (ppExpr x) ++ " == " ++ (ppExpr y)

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

mkTupleRepr :: [Some TypeRepr] -> Some TypeRepr
mkTupleRepr ts =
    go (reverse ts) Ctx.empty
        where go :: [Some TypeRepr] -> CtxRepr ctx -> Some TypeRepr
              go [] ctx = Some (TTupleRepr ctx)
              go ((Some tr):ts) ctx = go ts (ctx Ctx.%> tr)


getIth :: SomeExp -> Int -> SomeExp
getIth (SomeExp (TTupleRepr ctx) e) i 
 | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) =
     let tpr = ctx Ctx.! idx in
         SomeExp tpr (Expr (TupleGet ctx e idx tpr))
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

(|===|) :: (Typeable a, Eq a, Ord a, Show a, Read a, Data.Data a, SymWord a, HasKind a, SatModel a) => Expr (TEnum a) -> Expr (TEnum a) -> Expr TBool
e1 |===| e2 = Expr (EnumEq (TypeableType) e1 e2)

enumLit :: (Typeable a, Eq a, Ord a, Show a, Read a, Data.Data a, SymWord a, HasKind a, SatModel a) => a -> Expr (TEnum a)
enumLit a = Expr (EnumLit (TypeableValue a))

instance Boolean (Expr TBool) where
    true = Expr (BoolLit True)
    false = Expr (BoolLit False)
    bnot e = Expr (BoolNot e)
    (&&&) e1 e2 = Expr (BoolAnd e1 e2)
    (|||) e1 e2 = Expr (BoolOr e1 e2)

class SynEq (f :: k -> *) where
    synEq :: f a -> f b -> Bool

instance (SynEq f) => SynEq (App f) where
   synEq (IntLit i) (IntLit i2) = i == i2
   synEq  (IntAdd e1 e2) (IntAdd e1' e2') = (synEq e1 e1') && (synEq e2 e2')
   synEq  (IntMul e1 e2) (IntMul e1' e2') = (synEq e1 e1') && (synEq e2 e2')
   synEq  (IntNeg e1 ) (IntNeg e1' ) = (synEq e1 e1') 

   synEq  (BoolLit b) (BoolLit b') = b == b'
   synEq  (BoolAnd e1 e2) (BoolAnd e1' e2') = (synEq e1 e1') && (synEq e2 e2')
   synEq  (BoolOr e1 e2) (BoolOr e1' e2') = (synEq e1 e1') && (synEq e2 e2')
   synEq  (BoolXor e1 e2) (BoolXor e1' e2') = (synEq e1 e1') && (synEq e2 e2')
   synEq  (BoolNot e1 ) (BoolNot e1' ) = (synEq e1 e1') 

   synEq  (IntLe e1 e2) (IntLe e1' e2') = (synEq e1 e1') && (synEq e2 e2')
   synEq  (IntLt e1 e2) (IntLt e1' e2') = (synEq e1 e1') && (synEq e2 e2')
   synEq  (IntGt e1 e2) (IntGt e1' e2') = (synEq e1 e1') && (synEq e2 e2')
   synEq  (IntEq e1 e2) (IntEq e1' e2') = (synEq e1 e1') && (synEq e2 e2')
   synEq  (IntNeq e1 e2) (IntNeq e1' e2') = (synEq e1 e1') && (synEq e2 e2')

   synEq  (MkTuple repr asgn) (MkTuple repr1 asgn1) =
       case testEquality repr repr1 of
          Just Refl -> error "unimp"
          Nothing -> False
   synEq (TupleGet crepr e ind tr) (TupleGet crepr' e' ind' tr') =
    case (testEquality tr tr', testEquality crepr crepr') of
      (Just Refl, Just Refl) -> (synEq e e') && (ind == ind')
      _ -> False
    
   synEq (TupleSet repr e ind tup) (TupleSet repr' e' ind' tup') =
    case (testEquality repr repr') of
      Just Refl -> (synEq e e') && (Ctx.indexVal ind == Ctx.indexVal ind') && (synEq tup tup')
      Nothing -> False

   synEq  _ _ = False


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
                Nothing -> error $ "var not found in substitution: " ++ x
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
          go emap (Expr (TupleGet ctx tup ind etp)) = Expr (TupleGet ctx (go emap tup) ind etp)
          go emap (Expr (TupleSet ctx tup ind e)) = Expr (TupleSet ctx (go emap tup) ind (go emap e))
          go emap (Expr (EnumLit i)) = Expr (EnumLit i)
          go emap (Expr (EnumEq t a b)) = Expr (EnumEq t (go emap a) (go emap b))

someExprSub :: Map.Map String SomeExp -> SomeExp -> SomeExp
someExprSub emap e1 = 
    case e1 of
      (SomeExp tp e) ->
          SomeExp tp (exprSub emap e)

class FreeVar a where
    freeVars :: a -> Set.Set String

instance FreeVar (Expr tp) where

    freeVars (AtomExpr (Atom x tp)) = Set.singleton x 
    freeVars (Expr (IntLit _)) = Set.empty
    freeVars (Expr (IntAdd e1 e2)) = (freeVars e1) `Set.union` (freeVars e2)
    freeVars (Expr (IntMul e1 e2)) = (freeVars e1) `Set.union` (freeVars e2)
    freeVars (Expr (IntNeg e1 )) = (freeVars e1) 

    freeVars (Expr (BoolLit _)) = Set.empty
    freeVars (Expr (BoolAnd e1 e2)) = (freeVars e1) `Set.union` (freeVars e2)
    freeVars (Expr (BoolOr e1 e2)) = (freeVars e1) `Set.union` (freeVars e2)
    freeVars (Expr (BoolXor e1 e2)) = (freeVars e1) `Set.union` (freeVars e2)
    freeVars (Expr (BoolNot e1 )) = (freeVars e1) 

    freeVars (Expr (IntLe e1 e2)) = (freeVars e1) `Set.union` (freeVars e2)
    freeVars (Expr (IntLt e1 e2)) = (freeVars e1) `Set.union` (freeVars e2)
    freeVars (Expr (IntGt e1 e2)) = (freeVars e1) `Set.union` (freeVars e2)
    freeVars (Expr (IntEq e1 e2)) = (freeVars e1) `Set.union` (freeVars e2)
    freeVars (Expr (IntNeq e1 e2)) = (freeVars e1) `Set.union` (freeVars e2)

    freeVars (Expr (MkTuple _ asgn)) = Set.unions $ toListFC freeVars asgn
    freeVars (Expr (TupleGet _ tup _ _)) = freeVars tup
    freeVars (Expr (TupleSet _ tup _ e)) = (freeVars tup) `Set.union` (freeVars e)

    freeVars (Expr (EnumLit _)) = Set.empty
    freeVars (Expr (EnumEq _ a b)) = (freeVars a) `Set.union` (freeVars b)

instance FreeVar SomeExp where
    freeVars (SomeExp tp e) = freeVars e

instance (FreeVar a) => (FreeVar [a]) where
    freeVars as = Set.unions $ map freeVars as
