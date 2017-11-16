
module Prot.Lang.Command where
import Prot.Lang.Types
import Data.Type.Equality
import Prot.Lang.Expr

data Distr tp = Distr { distrName :: String, distrType :: TypeRepr tp }

data Command tp where
    Sampl :: forall tp tp2. String -> Distr tp2 -> Command tp -> Command tp
    Let :: forall tp tp2. String -> Expr tp2 -> Command tp -> Command tp
    Ite :: forall tp. Expr TBool -> Command tp -> Command tp -> Command tp
    Ret :: forall tp. Expr tp -> Command tp

cSampl :: String -> Distr tp2 -> Command tp -> Command tp
cSampl = Sampl

cLet :: String -> Expr tp2 -> Command tp -> Command tp
cLet = Let

cIte :: Expr TBool -> Command tp -> Command tp -> Command tp
cIte = Ite

cRet :: Expr tp -> Command tp
cRet = Ret



