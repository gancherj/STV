module Prot.Lang.Types where

import Data.Typeable
import Data.Type.Equality
import Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Ctx

data BaseType where
    BaseInt :: BaseType
    BaseBool :: BaseType

data BaseTypeRepr (tp :: BaseType) :: * where
    BaseIntRepr :: BaseTypeRepr BaseInt
    BaseBoolRepr :: BaseTypeRepr BaseBool

data Type where
    BaseToType :: BaseType -> Type
    TTuple :: Ctx Type -> Type
    -- TODO: Inject haskell types here, which could map to their symbolic enumeration in SBV.

type BaseToType = 'BaseToType
type TInt = BaseToType BaseInt
type TBool = BaseToType BaseBool
type TTuple = 'TTuple

data TypeRepr (t :: Type) :: * where
    TIntRepr :: TypeRepr TInt
    TBoolRepr :: TypeRepr TBool
    TTupleRepr :: !(Ctx.Assignment TypeRepr ctx) -> TypeRepr (TTuple ctx)


type CtxRepr = Ctx.Assignment TypeRepr
type BaseCtxRepr = Ctx.Assignment BaseTypeRepr

instance Show (TypeRepr tp) where
    show TIntRepr = "TInt"
    show TBoolRepr = "TBool"
    show (TTupleRepr t) = show t

instance ShowF TypeRepr

instance KnownRepr TypeRepr TInt where
    knownRepr = TIntRepr

instance KnownRepr TypeRepr TBool where
    knownRepr = TBoolRepr

type KnownCtx f = KnownRepr (Ctx.Assignment f)

instance KnownCtx TypeRepr ctx => KnownRepr TypeRepr (TTuple ctx) where
    knownRepr = TTupleRepr knownRepr

instance TestEquality TypeRepr where
    testEquality TIntRepr TIntRepr = Just Refl
    testEquality TBoolRepr TBoolRepr = Just Refl
    testEquality (TTupleRepr t) (TTupleRepr t') = 
        case (testEquality t t') of
          Just Refl -> Just Refl
          Nothing -> Nothing
    testEquality _ _ = Nothing


instance TestEquality BaseTypeRepr where
    testEquality BaseIntRepr BaseIntRepr = Just Refl
    testEquality BaseBoolRepr BaseBoolRepr = Just Refl
    testEquality _ _ = Nothing

instance Show (BaseTypeRepr tp) where
    show (BaseIntRepr) = "Int"
    show (BaseBoolRepr) = "Bool"

instance ShowF BaseTypeRepr where

-- utility functions
--

data AsBaseType tp where
    AsBaseType :: tp ~ BaseToType btp => BaseTypeRepr btp -> AsBaseType tp
    NotBaseType :: AsBaseType tp

asBaseType :: TypeRepr tp -> AsBaseType tp
asBaseType tp =
    case tp of
      TBoolRepr -> AsBaseType BaseBoolRepr
      TIntRepr -> AsBaseType BaseIntRepr
      _ -> NotBaseType

