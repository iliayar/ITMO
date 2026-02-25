import qualified Data.List as List

type Symb = String

infixl 4 :@

data Expr
  = Var Symb
  | Expr :@ Expr
  | Lam Symb Expr
  deriving (Eq, Read, Show)

data Term
  = Idx Int
  | Term :@: Term
  | Lmb Symb Term
  deriving (Read, Show)

type Context = [Symb]

-- перегруженное равенство, игнорирующее имя связываемой переменной
instance Eq Term where
  Idx m == Idx n = m == n
  (t1 :@: s1) == (t2 :@: s2) = t1 == t2 && s1 == s2
  Lmb _ t1 == Lmb _ t2 = t1 == t2
  _ == _ = False

shift :: Int -> Term -> Term
shift val term = shift' val 0 term
  where
    shift' :: Int -> Int -> Term -> Term
    shift' val base (Idx n)
      | n < base = Idx n
      | otherwise = Idx $ n + val
    shift' val base (l :@: r) = shift' val base l :@: shift' val base r
    shift' val base (Lmb sym b) = Lmb sym $ shift' val (base + 1) b

substDB :: Int -> Term -> Term -> Term
substDB j q (Idx n)
  | n < j = Idx n
  | n == j = shift n q
  | otherwise = Idx $ n - 1
substDB j q (l :@: r) = substDB j q l :@: substDB j q r
substDB j q (Lmb sym b) = Lmb sym $ substDB (j + 1) q b

betaRuleDB :: Term -> Term
betaRuleDB (Lmb sym t :@: s) = substDB 0 s t

oneStepDBN :: Term -> Maybe Term
oneStepDBN (Idx _) = Nothing
oneStepDBN t@((Lmb _ _) :@: _) = Just $ betaRuleDB t
oneStepDBN (l :@: r) = case oneStepDBN l of
  Nothing -> case oneStepDBN r of
    Nothing -> Nothing
    Just r' -> Just $ l :@: r'
  Just l' -> Just $ l' :@: r
oneStepDBN (Lmb sym t) = case oneStepDBN t of
  Nothing -> Nothing
  Just t' -> Just $ Lmb sym t'

oneStepDBA :: Term -> Maybe Term
oneStepDBA (Idx _) = Nothing
oneStepDBA t@((Lmb sym b) :@: a) = case oneStepDBA a of
  Nothing -> Just $ betaRuleDB t
  Just a' -> Just $ (Lmb sym b) :@: a'
oneStepDBA (l :@: r) = case oneStepDBA l of
  Nothing -> case oneStepDBA r of
    Nothing -> Nothing
    Just r' -> Just $ l :@: r'
  Just l' -> Just $ l' :@: r
oneStepDBA (Lmb sym t) = case oneStepDBA t of
  Nothing -> Nothing
  Just t' -> Just $ Lmb sym t'

nfDB :: (Term -> Maybe Term) -> Term -> Term
nfDB f t = case f t of
  Nothing -> t
  Just t' -> nfDB f t'

e2t :: Expr -> (Context, Term)
e2t exp = e2t' [] [] exp
  where
    e2t' :: [String] -> Context -> Expr -> (Context, Term)
    e2t' binded free (Var v) = case List.elemIndex v binded of
      Nothing -> case List.elemIndex v free of
        Nothing -> (free ++ [v], Idx $ length free + length binded)
        Just i -> (free, Idx $ i + length binded)
      Just i -> (free, Idx i)
    e2t' binded free (l :@ r) =
      let (free', l') = e2t' binded free l
          (free'', r') = e2t' binded free' r
       in (free'', l' :@: r')
    e2t' binded free (Lam v b) =
      let (free', b') = e2t' (v : binded) free b
       in (free', Lmb v b')

t2e :: Context -> Term -> Expr
t2e ctx t = t2e' [] ctx t
  where
    t2e' :: [String] -> Context -> Term -> Expr
    t2e' binded free (Idx i) =
      if i >= length binded
        then Var $ free !! (i - length binded)
        else Var $ binded !! i
    t2e' binded free (l :@: r) = (t2e' binded free l) :@ (t2e' binded free r)
    t2e' binded free (Lmb v b) =
      let v' = findFree binded v
       in Lam v' $ t2e' (v' : binded) free b

    findFree :: [String] -> String -> String
    findFree binded v
      | List.elem v binded = findFree binded $ v ++ "'"
      | otherwise = v
