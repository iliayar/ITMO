type Symb = String

infixl 4 :@:

infixr 3 :->

data Type
  = Boo
  | Type :-> Type
  deriving (Read, Show, Eq)

data Term
  = Fls
  | Tru
  | If Term Term Term
  | Idx Int
  | Term :@: Term
  | Lmb Symb Type Term
  deriving (Read, Show)

instance Eq Term where
  Fls == Fls = True
  Tru == Tru = True
  If b u w == If b1 u1 w1 = b == b1 && u == u1 && w == w1
  Idx m == Idx m1 = m == m1
  (u :@: w) == (u1 :@: w1) = u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1 = t == t1 && u == u1
  _ == _ = False

newtype Env = Env [(Symb, Type)]
  deriving (Read, Show, Eq)

shift :: Int -> Term -> Term
shift val term = shift' val 0 term
  where
    shift' :: Int -> Int -> Term -> Term
    shift' _ _ Fls = Fls
    shift' _ _ Tru = Tru
    shift' val base (If c tb eb) = If (shift' val base c) (shift' val base eb) (shift' val base eb)
    shift' val base (Idx n)
      | n < base = Idx n
      | otherwise = Idx $ n + val
    shift' val base (l :@: r) = shift' val base l :@: shift' val base r
    shift' val base (Lmb sym ty b) = Lmb sym ty $ shift' val (base + 1) b

substDB :: Int -> Term -> Term -> Term
substDB _ _ Fls = Fls
substDB _ _ Tru = Tru
substDB j q (If c tb eb) = If (substDB j q c) (substDB j q tb) (substDB j q eb)
substDB j q (Idx n)
  | n < j = Idx n
  | n == j = shift n q
  | otherwise = Idx $ n - 1
substDB j q (l :@: r) = substDB j q l :@: substDB j q r
substDB j q (Lmb sym ty b) = Lmb sym ty $ substDB (j + 1) q b

isValue :: Term -> Bool
isValue (Lmb _ _ _) = True
isValue Fls = True
isValue Tru = True
isValue _ = False

betaRuleDB :: Term -> Term
betaRuleDB (Lmb sym _ t :@: s) = substDB 0 s t

oneStep :: Term -> Maybe Term
oneStep (If Tru tb _) = Just tb
oneStep (If Fls _ eb) = Just eb
oneStep (If c tb eb) = case oneStep c of
  Nothing -> Nothing
  Just c' -> Just $ If c' tb eb
oneStep t@((Lmb sym ty b) :@: a) = case oneStep a of
  Nothing ->
    if isValue a
      then Just $ betaRuleDB t
      else Nothing
  Just a' -> Just $ (Lmb sym ty b) :@: a'
oneStep (l :@: r) = case oneStep l of
  Nothing -> Nothing
  Just l' -> Just $ l' :@: r
oneStep _ = Nothing

whnf :: Term -> Term
whnf t =
  case oneStep t of
    Nothing -> t
    Just t' -> whnf t'

infer :: Env -> Term -> Maybe Type
infer = infer' []
    where 
        infer' :: [Type] -> Env -> Term -> Maybe Type
        infer' ctx env Tru = Just Boo
        infer' ctx env Fls = Just Boo
        infer' ctx env (If c t e) = case (infer' ctx env c, infer' ctx env t, infer' ctx env e) of
          (Just Boo, Just tyl, Just tye) | tyl == tye -> Just tyl
          _ -> Nothing
        infer' ctx (Env env) (Idx i) = 
            if i >= length ctx then Just $ snd $ env !! (i - length ctx)
            else Just $ ctx !! i
        infer' ctx env (Lmb v ty b) = case infer' (ty : ctx) env b of
            Nothing -> Nothing
            Just tyb -> Just $ ty :-> tyb
        infer' ctx env (l :@: r) = case (infer' ctx env l, infer' ctx env r) of
            (Just (tya :-> tyr), Just tya') | tya == tya' -> Just tyr
            _ -> Nothing

infer0 :: Term -> Maybe Type
infer0 = infer $ Env []
