
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

instance TypeOf Command where
    typeOf (Sampl x d args k) = typeOf k
    typeOf (Let x e k) = typeOf k
    typeOf (Ite e c1 c2) = typeOf c2
    typeOf (Ret e) = typeOf e

printTabs :: Int -> String
printTabs 0 = ""
printTabs i = "    " ++ (printTabs (i-1))

ppCommand' :: Int -> Command tp -> String
ppCommand' i (Sampl x d args k) =
    (printTabs i) ++ x ++ " <- " ++ (ppDistr d) ++ " [" ++ concatMap ppSomeExp args ++ "];\n" ++ (ppCommand' i k)
ppCommand' i (Let x e k) =
    (printTabs i) ++ "let " ++ x ++ " = " ++ (ppExpr e) ++ ";\n" ++ (ppCommand' i k)
ppCommand' i (Ite b e1 e2) =
    (printTabs i) ++ "if " ++ (ppExpr b) ++ " then \n" ++ (ppCommand' (i + 1) e1) ++ "\n" ++ (printTabs i) ++ "else \n" ++ (ppCommand' (i+1) e2)
ppCommand' i (Ret e) = (printTabs i) ++ "ret " ++ (ppExpr e)

ppCommand = ppCommand' 0

chainCommand :: Command tp -> (Expr tp -> Command tp2) -> Command tp2
chainCommand (Sampl x d es k) c2 = Sampl x d es (chainCommand k c2)
chainCommand (Let x e k) c2 = Let x e (chainCommand k c2)
chainCommand (Ite e k1 k2) c2 = Ite e (chainCommand k1 c2) (chainCommand k2 c2)
chainCommand (Ret e) c2 = c2 e


