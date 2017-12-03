
module Prot.Lang.Command where
import Prot.Lang.Types
import Data.Type.Equality
import Prot.Lang.Expr

data Distr tp where
    SymDistr :: String -> TypeRepr tp -> (Expr tp -> [SomeExp] -> [Expr TBool]) -> Distr tp
    UnifInt :: Integer -> Integer -> Distr TInt
    UnifBool :: Distr TBool

compareDistr :: Distr tp -> Distr tp1 -> Bool
compareDistr (UnifInt i1 i2) (UnifInt i1' i2') = (i1 == i1') && (i2 == i2')
compareDistr (UnifBool) (UnifBool) = True
compareDistr (SymDistr x tp _) (SymDistr y tp2 _) = -- constraint functions not compared. 
    case testEquality tp tp2 of
      Just Refl -> x == y
      Nothing -> False
compareDistr _ _ = False

ppDistr :: Distr tp -> String
ppDistr (SymDistr x _ _) = x
ppDistr (UnifInt i1 i2) = "[" ++ (show i1) ++ ", " ++ (show i2) ++ "]"
ppDistr (UnifBool) = "{0,1}"

mkDistr :: String -> TypeRepr tp -> (Expr tp -> [SomeExp] -> [Expr TBool]) -> Distr tp
mkDistr = SymDistr

unifInt :: Integer -> Integer -> Distr TInt
unifInt = UnifInt

unifBool :: Distr TBool
unifBool = UnifBool

getConds :: String -> [SomeExp] -> Distr tp -> [Expr TBool]
getConds x es (SymDistr _ tp cs) = cs (mkAtom x tp) es
getConds x [] (UnifInt i1 i2) = 
    let xv = mkAtom x TIntRepr in
    [Expr $ IntLe (Expr $ IntLit i1) xv, Expr $ IntLe xv (Expr $ IntLit i2)]
getConds x [] (UnifBool) = []
getConds _ _ _ = error "bad distr call!"

instance TypeOf Distr where
    typeOf (SymDistr x t _) = t
    typeOf (UnifInt _ _) = TIntRepr
    typeOf (UnifBool) = TBoolRepr


data Command tp where
    Sampl :: forall tp tp2. String -> Distr tp2 -> [SomeExp] -> Command tp -> Command tp
    Let :: forall tp tp2. String -> Expr tp2 -> Command tp -> Command tp
    Ite :: forall tp. Expr TBool -> Command tp -> Command tp -> Command tp
    Ret :: forall tp. Expr tp -> Command tp

data SomeCommand = forall tp. SomeCommand (TypeRepr tp) (Command tp)


ppCommand :: Command tp -> String
ppCommand (Sampl x d args k) =
    x ++ " <- " ++ (ppDistr d) ++ concatMap ppSomeExp args ++ ";\n" ++ (ppCommand k)
ppCommand (Let x e k) =
    "let " ++ x ++ " = " ++ (ppExpr e) ++ ";\n" ++ (ppCommand k)
ppCommand (Ite b e1 e2) =
    "if " ++ (ppExpr b) ++ " then " ++ (ppCommand e1) ++ " else " ++ (ppCommand e2)
ppCommand (Ret e) = "ret " ++ (ppExpr e)

chainCommand :: Command tp -> (Expr tp -> Command tp2) -> Command tp2
chainCommand (Sampl x d es k) c2 = Sampl x d es (chainCommand k c2)
chainCommand (Let x e k) c2 = Let x e (chainCommand k c2)
chainCommand (Ite e k1 k2) c2 = Ite e (chainCommand k1 c2) (chainCommand k2 c2)
chainCommand (Ret e) c2 = c2 e


