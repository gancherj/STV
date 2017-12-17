module Prot.Lang.Analyze where
import Prot.Lang.Command
import Prot.Lang.Types
import Prot.Lang.Expr
import Data.List
import Data.SBV
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data Sampling = forall tp. Sampling { _sampdistr :: Distr tp, _sampname :: String, _sampargs :: [SomeExp] }

data PartialLeaf ret where
    PartialLeaf :: {
        _pLeafSamps :: [Sampling],
        _pLeafConds :: [Expr TBool],
        _pLeafCont :: Command ret} -> PartialLeaf ret

transPartialLeaf :: ([Sampling] -> [Expr TBool] -> Expr TBool -> IO Int) -> PartialLeaf ret -> IO [PartialLeaf ret]
transPartialLeaf check (PartialLeaf samps conds k) =
    case k of
      Ret e -> return [PartialLeaf samps conds (Ret e)] -- done if hit bottom
      Sampl x d args k' -> transPartialLeaf check $ PartialLeaf ((Sampling d x args):samps) ((getConds x args d) ++ conds) k'
      Ite b e1 e2 -> do
          ret <- check samps conds b
          case ret of
            0 -> transPartialLeaf check $  PartialLeaf samps conds e1 -- b is satisfiable but (not b) is not
            1 -> transPartialLeaf check $ PartialLeaf samps conds e2 -- b is unsatisfiable but (not b) is satisfiable
            _ -> do -- both b and (not b) are satisfiable
                ls1 <- transPartialLeaf check $ PartialLeaf samps (b:conds) e1
                ls2 <- transPartialLeaf check $ PartialLeaf samps ((Expr (BoolNot b)):conds) e2
                return (ls1 ++ ls2)

getLeaves :: [PartialLeaf ret] -> [Leaf ret]
getLeaves lvs = map go lvs
    where
        go :: PartialLeaf ret -> Leaf ret
        go (PartialLeaf samps conds (Ret e)) = Leaf samps conds e
        go _ = error "bad partial leaf!"


commandToLeaves :: ([Sampling] -> [Expr TBool] -> Expr TBool -> IO Int) -> Command ret -> IO [Leaf ret]
commandToLeaves check c = do
    plvs <- transPartialLeaf check (PartialLeaf [] [] c)
    return $ getLeaves plvs
    
   


-- Final Leaves

-- equality is syntactic
instance Eq Sampling where
    (==) (Sampling distr name args) (Sampling distr' name' args') =
        (compareDistr distr distr') && (name == name') && (args == args')

ppSampling :: Sampling -> String
ppSampling (Sampling d x es) = x ++ " <- " ++ (ppDistr d) ++ " " ++ (concatMap (\e -> "(" ++ ppSomeExp e ++ ")") es) 

data Leaf ret where
    Leaf :: {
        _leafSamps :: [Sampling],
        _leafConds :: [Expr TBool],
        _leafRet :: Expr ret } -> Leaf ret

ppLeaf :: Leaf ret -> String
ppLeaf (Leaf samps conds ret) = "Samplings: " ++ (concatMap ppSampling samps) ++ "\n Conds:" ++  (concatMap (\e -> (ppExpr e) ++ " ") conds) ++ "\n Ret: " ++ (ppExpr ret) ++ "\n \n"

ppLeaves :: [Leaf ret] -> String
ppLeaves e = concatMap ppLeaf e

    
instance Show (Leaf rtp) where
    show (Leaf samps conds ret) =
        "Samplings: " ++ (concatMap ppSampling samps) ++ "\n Conds:" ++  (concatMap (\e -> (ppExpr e) ++ " ") conds) ++ "\n Ret: " ++ (ppExpr ret) ++ "\n \n"



------
--
--



freeSampsBy :: Set.Set String -> [Sampling] -> [Sampling]
freeSampsBy varsSeen = filter (\s -> Set.null (freeVars (_sampargs s) Set.\\ varsSeen))

samplingsToDag :: [Sampling] -> [[Sampling]]
samplingsToDag ss =
    go Set.empty ss
        where
            go :: Set.Set String -> [Sampling] -> [[Sampling]]
            go varsSeen ss =
                let freeSamps = freeSampsBy varsSeen ss in
                case freeSamps of
                  [] -> if null ss then [] else error $ "bad: still have sampls " ++ (show (map ppSampling ss)) ++ " with varsSeen " ++ show varsSeen
                  ls -> 
                      let nextLvls = go (Set.union varsSeen (Set.fromList (map _sampname freeSamps))) (ss \\ freeSamps) in
                      (freeSamps : nextLvls)

sampNamesByLevel :: [[Sampling]] -> [Set.Set String]
sampNamesByLevel dag = map (\lvl -> Set.fromList (map _sampname lvl)) dag

sampNamesCumul_ :: [Set.Set String] -> [Set.Set String]
sampNamesCumul_ ns =
    case ns of
      (s : ss) -> 
          s : (sampNamesCumul_ (map (Set.union s) ss))
      [] -> []

sampNamesCumul :: [[Sampling]] -> [Set.Set String]
sampNamesCumul = sampNamesCumul_ . sampNamesByLevel

condsCumul :: [Expr TBool] -> [Set.Set String] -> [[Expr TBool]]
condsCumul es [] = []
condsCumul es (l:ls) =
    (filter (\e -> Set.isSubsetOf (freeVars e) l) es) : (condsCumul es ls)



data LeafDag ret where
    LeafDag :: {
        _leafSampDag :: [[Sampling]],
        _leafCondsByLvl :: [[Expr TBool]],
        _leafDagRet :: Expr ret} -> LeafDag ret

mkDag :: Leaf ret -> LeafDag ret
mkDag (Leaf samps conds ret) =
    LeafDag dag (condsCumul conds (sampNamesCumul dag)) ret
        where
            dag = samplingsToDag samps

dagCompatible :: LeafDag ret -> LeafDag ret -> Bool
dagCompatible (LeafDag dag _ _) (LeafDag dag' _ _) | length dag /= length dag' = False
                                                   | otherwise =
                                                       bAnd $ map (\(l1,l2) -> length l1 == length l2) (zip dag dag')

dagCondLevel :: LeafDag ret -> Int -> [Expr TBool]
dagCondLevel d i | i >= length (_leafCondsByLvl d) = error "bad i"
                 | otherwise = (_leafCondsByLvl d) !! i

dagRank :: LeafDag ret -> Int
dagRank d = length (_leafSampDag d)

ppLeafDags :: [LeafDag ret] -> String
ppLeafDags dags = concatMap (\dag -> go dag ++ "\n") dags
    where
        go :: LeafDag ret -> String
        go (LeafDag sampdag conds ret) =
            case sampdag of
              [] -> "Empty dag with ret = " ++ ppExpr ret
              _ ->
                "Sampling dag: (depth " ++ (show $ length sampdag) ++ ") \n" ++
                concatMap (\samplings -> concatMap (\sampling -> (ppSampling sampling) ++ ", ") samplings ++ "\n") sampdag ++
                "Final cond: \n" ++
                    concatMap (\cond -> ppExpr cond ++ "\n") (last conds) ++
                "Ret: " ++ ppExpr ret ++ "\n"



            
