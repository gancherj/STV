
data Chan m i = Chan (TypeRepr m) (NatRepr i)

chanId :: Chan m i -> Some NatRepr
chanId (Chan tp nr) = Some nr

mkChan :: TypeRepr m -> NatRepr i -> Chan m i
mkChan = Chan 

data ChansRepr (cs :: [*]) where
    EmptyChansRepr :: ChansRepr '[]
    ConsChansRepr :: NatRepr w -> ChansRepr cs -> ChansRepr ((NatRepr w) ': cs)

chansContain :: ChansRepr cs -> NatRepr w -> Bool
chansContain (EmptyChansRepr) _ = False
chansContain (ConsChansRepr w c) w' =
    case (testEquality w w') of
      Just Refl -> True
      _ -> chansContain c w'

instance TestEquality ChansRepr where
    testEquality (EmptyChansRepr) (EmptyChansRepr) = Just Refl
    testEquality (EmptyChansRepr) (ConsChansRepr _ _) = Nothing
    testEquality (ConsChansRepr _ _) (EmptyChansRepr) = Nothing
    testEquality (ConsChansRepr w c) (ConsChansRepr w' c') = 
        case (testEquality w w', testEquality c c') of
          (Just Refl, Just Refl) -> Just Refl
          _ -> Nothing

instance OrdF ChansRepr where
    compareF (EmptyChansRepr) (EmptyChansRepr) = EQF
    compareF (EmptyChansRepr) (ConsChansRepr _ _) = LTF
    compareF (ConsChansRepr _ _) (EmptyChansRepr) = GTF
    compareF (ConsChansRepr w c) (ConsChansRepr w' c') =
        case (compareF w w') of
          LTF -> LTF
          GTF -> GTF
          EQF -> 
              case (compareF c c') of
                LTF -> LTF
                GTF -> GTF
                EQF -> EQF


class KnownChansRepr (cs :: [*]) where
    knownChansRepr :: ChansRepr cs

instance KnownChansRepr '[] where
    knownChansRepr = EmptyChansRepr

instance (KnownChansRepr cs, KnownNat w) => KnownChansRepr ((NatRepr w) ': cs) where
    knownChansRepr = ConsChansRepr knownNat knownChansRepr

type KnownChans ins outs = (KnownChansRepr ins, KnownChansRepr outs)

unionChanReprs :: ChansRepr cs -> ChansRepr cs2 -> ChansRepr (Union cs cs2)
unionChanReprs (EmptyChansRepr) c = c
unionChanReprs (ConsChansRepr w c) c' =
    insertChanReprs w (unionChanReprs c c')

insertChanReprs :: NatRepr w -> ChansRepr cs -> ChansRepr (Insert (NatRepr w) cs)
insertChanReprs w (EmptyChansRepr) = ConsChansRepr w EmptyChansRepr
insertChanReprs a (ConsChansRepr x xs) =
    case testEquality a x of
      Just Refl ->
          ConsChansRepr a xs
      Nothing -> 
          unsafeCoerce $ ConsChansRepr x (insertChanReprs a xs) -- TODO can i fix this?


data SomeChan = forall m i. SomeChan (Chan m i)

chanListToRepr :: [SomeChan] -> Some ChansRepr
chanListToRepr [] = Some EmptyChansRepr
chanListToRepr ((SomeChan (Chan _ nr)):cs) =
    ConsChansRepr nr (chanListToRepr cs)


type ChanReprs ins outs = (ChansRepr ins, ChansRepr outs)


data Process (s :: Type) (ins :: [*]) (outs :: [*]) (a :: Type) where
    PBind :: (KnownRepr TypeRepr b) => ChanReprs ins2 outs2 -> (Expr a -> Process s ins2 outs2 b) -> Process s ins outs a -> Process s (Union ins ins2) (Union outs outs2) b
    PRet :: ChanReprs ins outs -> Expr a -> Process s ins outs a
    Send :: Chan m i -> Expr m -> Process s '[] '[NatRepr i] TUnit
    Recv :: Chan m i -> Process s '[NatRepr i] '[] m 
    Store :: ChanReprs ins outs -> Expr s -> Process s ins outs TUnit
    Get :: (KnownRepr TypeRepr s) => ChanReprs ins outs -> Process s ins outs s
    Samp :: (KnownRepr TypeRepr tp) => ChanReprs ins outs -> Dist (Expr tp) -> Process s ins outs tp
    Ite ::
        Expr TBool -> Process se ins outs a -> Process se ins2 outs2 a -> Process se (Union ins ins2) (Union outs outs2) a
    LoopFor :: Int -> Process se ins outs TUnit -> Process se ins outs TUnit

instance TypeOf (Process s ins outs) where
    typeOf (PRet _ a) = typeOf a
    typeOf (Send _ _) = TUnitRepr
    typeOf (Recv (Chan tp _)) = tp
    typeOf (Store _ _) = TUnitRepr
    typeOf (Get _ ) = knownRepr
    typeOf (Samp _ d) = knownRepr
    typeOf (Ite _ k _) = typeOf k
    typeOf (LoopFor _ _) = TUnitRepr
    typeOf (PBind _ _ _) = knownRepr



chansOf :: forall (ins :: [*]) (outs :: [*]) s a. Process s ins outs a -> (ChansRepr ins, ChansRepr outs)
chansOf (PBind (c1,c2) f k) = 
    let (a,c) = chansOf k in
    (unionChanReprs a c1, unionChanReprs c c2)
chansOf (PRet cr _) = cr
chansOf (Send (Chan _ c) _) = (EmptyChansRepr, ConsChansRepr c EmptyChansRepr)
chansOf (Recv (Chan _ c)) = (ConsChansRepr c EmptyChansRepr, EmptyChansRepr)
chansOf (Store cr _) = cr
chansOf (Get cr) = cr
chansOf (Samp cr _) = cr
chansOf (Ite _ k1 k2) =
    let (a,b) = chansOf k1
        (c,d) = chansOf k2 in
    (unionChanReprs a c, unionChanReprs b d)
chansOf (LoopFor _ k) = chansOf k


data Party (st :: Type) (a :: Type) = forall (ins :: [*]) (outs :: [*]). Party {
  pSt :: Expr st,
  pProc :: Process st ins outs a 
}

partyChans :: Party st a -> (Some ChansRepr, Some ChansRepr)
partyChans (Party _ p) =
    let (a,b) = chansOf p in (Some a, Some b)


msgCompatible :: Chan m i -> (Some NatRepr, SomeExp) -> Bool
msgCompatible (Chan tp2 nr2) (Some (nr), (SomeExp tp e)) =
    case (testEquality nr nr2, testEquality tp tp2) of
      (Just Refl, Just Refl) -> True
      _ -> False

findRemove :: (a -> Bool) -> [a] -> Maybe (a, [a])
findRemove f [] = Nothing
findRemove f (x : xs) =
    case (f x) of
      True -> return (x, xs)
      False -> do
          (resa, resxs) <- findRemove f xs
          return (resa, x : resxs)



execParty' :: [(Some NatRepr, SomeExp)] -> Some (Party s) -> Dist ([(Some NatRepr, SomeExp)], Either (Expr s, SomeExp) (Some (Party s)))
execParty' q (Some p@(Party st proc)) =
  case proc of
    PRet _ a -> return (q, Left (st, mkSome a))
    Send c e ->
        return ((chanId c, mkSome e):q, Left (st, mkSome unitExp))
    Recv c@(Chan ctp _) ->
        case (findRemove (msgCompatible c) q) of
          Just ((Some (qnr), SomeExp qtp qe), qrest) ->
              case testEquality ctp qtp of
                Just Refl ->
                    return (qrest, Left (st, mkSome qe))
                Nothing -> error "type error"
          Nothing -> return (q, Right (Some p))
    Store _ s ->
        return (q, Left (s, mkSome unitExp))
    Get _ ->
        return (q, Left (st, mkSome st))
    Samp _ d -> do
        x <- d
        return (q, Left (st, mkSome x))
    Ite e k1 k2 -> do
        dIte e (execParty' q (Some $ Party st k1)) (execParty' q (Some $ Party st k2))
    LoopFor 1 k ->
        execParty' q (Some $ Party st k)
    LoopFor i k  ->
        execParty' q (Some $ Party st (PBind (chansOf k) (\_ -> LoopFor (i-1) k) k))
    PBind cr f ma -> do
        (qnew, res) <- execParty' q (Some $ Party st ma)
        case res of
          Left (stnew, a) -> 
              case a of
                SomeExp atp ae -> 
                    case (testEquality atp (typeOf ma)) of
                      Just Refl -> execParty' qnew (Some $ Party stnew (f ae))
                      Nothing -> error "type error"
          Right pnew -> 
              case pnew of
                Some (Party stnew procnew) ->
                    case (testEquality (typeOf ma) (typeOf procnew)) of
                      Just Refl ->
                        return (qnew, Right $ Some $ Party stnew (PBind cr f procnew))
                      Nothing -> error "type error"

execParty :: [(Some NatRepr, SomeExp)] -> Party s TUnit -> Dist ([(Some NatRepr, SomeExp)], Maybe (Party s TUnit))
execParty q p = do
    (q', res) <- execParty' q (Some p)
    case res of
      Left (s,_) -> return (q', Nothing)
      Right p -> 
          case p of
            Some p@(Party st pr) ->
                case (testEquality (typeOf pr) TUnitRepr) of
                  Just Refl -> return (q', Just p)
                  Nothing -> error "type error"

data SomeParty = forall st. SomeParty (Party st TUnit)

data MPS (ins :: [*]) (outs :: [*]) where
    MPSEmpty :: MPS '[] '[]
    -- new ins (ins, outs, ins', outs') -> (ins ++ ins') \\ (outs ++ outs')
    --
    MPSExtend :: Process st ins outs TUnit -> Expr st -> MPS mins mouts -> MPS (Difference (Union ins mins) (Union outs mouts)) (Difference (Union outs mouts) (Union ins mins))

type MPSMap = Map.Map (Some ChansRepr) (Maybe SomeParty)

mpsToMap :: MPS ins outs -> MPSMap
mpsToMap (MPSEmpty) = Map.empty
mpsToMap (MPSExtend p s m) =
    let (c,_) = chansOf p in
    Map.insert (Some c) (Just $ SomeParty (Party s p)) (mpsToMap m)

findMPSParty :: NatRepr w -> Map.Map (Some ChansRepr) (Maybe SomeParty) -> Maybe (Some ChansRepr, Maybe SomeParty)
findMPSParty w m = do
    k <- find (\(Some k) -> chansContain k w) (Map.keys m)
    p <- Map.lookup k m
    return (k, p)

findOutput :: [(Some NatRepr, SomeExp)] -> Maybe (Expr TBool)
findOutput q  = do
    (_, SomeExp tr e) <- find (\(Some nr, SomeExp tr e) ->
        case (testEquality nr (knownNat :: NatRepr 1), testEquality tr TBoolRepr) of
          (Just Refl, Just Refl) -> True
          _ -> False) q
    case (testEquality tr TBoolRepr) of
      Just Refl -> Just e
      Nothing -> error "absurd"


-- Channel 1 is reserved for output of distinguisher
runMPS :: [(Some NatRepr, SomeExp)] -> MPSMap -> Dist (Expr TBool)
runMPS q pmap | Just b <- findOutput q = return b
              | otherwise =
                  let (snr, se) = head q in
                  case snr of 
                    Some w -> case (findMPSParty w pmap) of
                                Just (k, mp) -> 
                                    case mp of
                                      Just (SomeParty p) -> do
                                        (qres, pk) <- execParty q p
                                        case pk of
                                          Just p' ->
                                              runMPS qres (Map.insert k (Just $ SomeParty p) pmap)
                                          Nothing ->
                                              runMPS qres (Map.insert k (Nothing) pmap)
                                      Nothing -> fail "recipient is done"
                                Nothing -> fail "no recipient"

--mkSymDist :: Int -> ChansRepr d2p -> ChansRepr p2d -> Party TUnit TUnit
--mkSymDist i cr1 cr2 = Party unitExp (go i cr1 cr2)
--    where
--        go :: Int -> ChansRepr d2p -> ChansRepr p2d -> Process TUnit p2d d2p TUnit
--        go i outs ins =

