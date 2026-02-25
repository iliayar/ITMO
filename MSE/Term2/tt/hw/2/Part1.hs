import Control.Monad (guard)

type Symb = String

infixl 4 :@:

infixr 3 :->

infixl 5 :*

infixl 4 :+

data Type
  = Boo
  | Nat
  | Type :-> Type
  | Type :* Type
  | Type :+ Type
  deriving (Read, Show, Eq)

data Pat
  = PVar Symb
  | PPair Pat Pat
  deriving (Read, Show, Eq)

data Term
  = Fls
  | Tru
  | If Term Term Term
  | Zero
  | Succ Term
  | Pred Term
  | IsZero Term
  | Idx Int
  | Term :@: Term
  | Lmb Symb Type Term
  | Let Pat Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  | Fix Term
  | Inl Term Type
  | Inr Type Term
  | Case Term Symb Term Term
  deriving (Read, Show)

instance Eq Term where
  Fls == Fls = True
  Tru == Tru = True
  If b u w == If b1 u1 w1 = b == b1 && u == u1 && w == w1
  Zero == Zero = True
  Succ u == Succ u1 = u == u1
  Pred u == Pred u1 = u == u1
  IsZero u == IsZero u1 = u == u1
  Idx m == Idx m1 = m == m1
  (u :@: w) == (u1 :@: w1) = u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1 = t == t1 && u == u1
  Let p u w == Let p1 u1 w1 = p == p1 && u == u1 && w == w1
  Pair u w == Pair u1 w1 = u == u1 && w == w1
  Fst z == Fst z1 = z == z1
  Snd z == Snd z1 = z == z1
  Fix u == Fix u1 = u == u1
  Inl u t == Inl u1 t1 = u == u1 && t == t1
  Inr t u == Inr t1 u1 = t == t1 && u == u1
  Case u _ t s == Case u1 _ t1 s1 = u == u1 && t == t1 && s == s1
  _ == _ = False

newtype Env = Env [(Symb, Type)]
  deriving (Read, Show, Eq)

isNV :: Term -> Bool
isNV Zero = True
isNV (Succ v) = isNV v
isNV _ = False

countBinds :: Pat -> Int
countBinds (PVar _) = 1
countBinds (PPair l r) = countBinds l + countBinds r

shift :: Int -> Term -> Term
shift val term = shift' val 0 term
  where
    shift' :: Int -> Int -> Term -> Term
    shift' _ _ Fls = Fls
    shift' _ _ Tru = Tru
    shift' val base (If c tb eb) = If (shift' val base c) (shift' val base tb) (shift' val base eb)
    shift' val base (Idx n)
      | n < base = Idx n
      | otherwise = Idx $ n + val
    shift' val base (l :@: r) = shift' val base l :@: shift' val base r
    shift' val base (Lmb sym ty b) = Lmb sym ty $ shift' val (base + 1) b
    shift' val base (Let pat init body) =
      let cnt = countBinds pat
       in Let pat (shift' val base init) (shift' val (base + cnt) body)
    shift' val base (Fst p) = Fst $ shift' val base p
    shift' val base (Snd p) = Snd $ shift' val base p
    shift' val base (Pair l r) = Pair (shift' val base l) (shift' val base r)
    shift' val base Zero = Zero
    shift' val base (Succ t) = Succ $ shift' val base t
    shift' val base (Pred t) = Pred $ shift' val base t
    shift' val base (IsZero t) = IsZero $ shift' val base t
    shift' val base (Fix t) = Fix $ shift' val base t
    shift' val base (Inl t ty) = Inl (shift' val base t) ty
    shift' val base (Inr ty t) = Inr ty $ shift' val base t
    shift' val base (Case t sym l r) =
      Case (shift' val base t) sym (shift' val (base + 1) l) (shift' val (base + 1) r)

substDB :: Int -> Term -> Term -> Term
substDB _ _ Fls = Fls
substDB _ _ Tru = Tru
substDB j q (If c tb eb) = If (substDB j q c) (substDB j q tb) (substDB j q eb)
substDB j q (Idx n)
  | n == j = q
  | otherwise = Idx n
substDB j q (l :@: r) = substDB j q l :@: substDB j q r
substDB j q (Lmb sym ty b) = Lmb sym ty $ substDB (j + 1) (shift 1 q) b
substDB j q (Let pat init body) =
  let cnt = countBinds pat
   in Let pat (substDB j q init) $ substDB (j + cnt) (shift cnt q) body
substDB j q (Pair l r) = Pair (substDB j q l) (substDB j q r)
substDB j q (Fst p) = Fst $ substDB j q p
substDB j q (Snd p) = Snd $ substDB j q p
substDB j q Zero = Zero
substDB j q (Succ t) = Succ $ substDB j q t
substDB j q (Pred t) = Pred $ substDB j q t
substDB j q (IsZero t) = IsZero $ substDB j q t
substDB j q (Fix t) = Fix $ substDB j q t
substDB j q (Inl t ty) = Inl (substDB j q t) ty
substDB j q (Inr ty t) = Inr ty (substDB j q t)
substDB j q (Case t sym l r) =
  Case (substDB j q t) sym (substDB (j + 1) (shift 1 q) l) (substDB (j + 1) (shift 1 q) r)

isValue :: Term -> Bool
isValue (Lmb _ _ _) = True
isValue Fls = True
isValue Tru = True
isValue (Pair l r) = isValue l && isValue r
isValue (Inl t _) = isValue t
isValue (Inr _ t) = isValue t
isValue t
  | isNV t = True
  | otherwise = False

match :: Pat -> Term -> Maybe [(Symb, Term)]
match (PVar sym) t = do
  guard $ isValue t
  return [(sym, t)]
match (PPair lp rp) p@(Pair l r) = do
  guard $ isValue p
  ls <- match lp l
  ps <- match rp r
  return $ ls ++ ps
match _ _ = Nothing

oneStep :: Term -> Maybe Term
oneStep (If Tru tb _) = Just tb
oneStep (If Fls _ eb) = Just eb
oneStep (If c tb eb) = case oneStep c of
  Nothing -> Nothing
  Just c' -> Just $ If c' tb eb
oneStep t@((Lmb sym ty b) :@: a) = case oneStep a of
  Nothing ->
    if isValue a
      then Just $ shift (-1) $ substDB 0 (shift 1 a) b
      else Nothing
  Just a' -> Just $ (Lmb sym ty b) :@: a'
oneStep (l :@: r) = case oneStep l of
  Nothing -> Nothing
  Just l' -> Just $ l' :@: r
oneStep (Let pat init body) = case oneStep init of
  Nothing ->
    if isValue init
      then case match pat init of
        Nothing -> Nothing
        Just vs ->
          Just $
            foldr (\(_, v) body -> shift (-1) $ substDB 0 (shift 1 v) body) body vs
      else Nothing
  Just init' -> Just $ Let pat init' body
oneStep (Pair l r) = case oneStep l of
  Nothing ->
    if not $ isValue l
      then Nothing
      else fmap (Pair l) $ oneStep r
  Just l' -> Just $ Pair l' r
oneStep (Fst p@(Pair l _)) =
  if isValue p
    then Just l
    else fmap Fst $ oneStep p
oneStep (Snd p@(Pair _ r)) =
  if isValue p
    then Just r
    else fmap Snd $ oneStep p
oneStep (Fst p) = fmap Fst $ oneStep p
oneStep (Snd p) = fmap Snd $ oneStep p
oneStep (Succ v) = fmap Succ $ oneStep v
oneStep (Pred Zero) = Just Zero
oneStep (Pred succ@(Succ nv)) =
  if isNV nv
    then Just nv
    else fmap Pred $ oneStep succ
oneStep (Pred t) = fmap Pred $ oneStep t
oneStep (IsZero Zero) = Just Tru
oneStep (IsZero succ@(Succ nv)) =
  if isNV nv
    then Just Fls
    else fmap IsZero $ oneStep succ
oneStep (IsZero t) = fmap IsZero $ oneStep t
oneStep fix@(Fix (Lmb _ _ body)) = Just $ shift (-1) $ substDB 0 (shift 1 fix) body
oneStep (Fix t) = fmap Fix $ oneStep t
oneStep (Case t sym l r) = case oneStep t of
  Just t' -> Just $ Case t' sym l r
  Nothing | not $ isValue t -> Nothing
  Nothing -> case t of
    (Inl t' _) -> Just $ shift (-1) $ substDB 0 (shift 1 t') l
    (Inr _ t') -> Just $ shift (-1) $ substDB 0 (shift 1 t') r
oneStep (Inl t ty) = case oneStep t of
  Nothing -> Nothing
  Just t' -> Just $ Inl t' ty
oneStep (Inr ty t) = case oneStep t of
  Nothing -> Nothing
  Just t' -> Just $ Inr ty t'
oneStep _ = Nothing

whnf :: Term -> Term
whnf t =
  case oneStep t of
    Nothing -> t
    Just t' -> whnf t'

checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar sym) ty = Just $ Env [(sym, ty)]
checkPat (PPair lp rp) (lty :* rty) = do
  Env le <- checkPat lp lty
  Env re <- checkPat rp rty
  return $ Env $ re ++ le
checkPat _ _ = Nothing

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
      if i >= length ctx
        then Just $ snd $ env !! (i - length ctx)
        else Just $ ctx !! i
    infer' ctx env (Lmb v ty b) = case infer' (ty : ctx) env b of
      Nothing -> Nothing
      Just tyb -> Just $ ty :-> tyb
    infer' ctx env (l :@: r) = case (infer' ctx env l, infer' ctx env r) of
      (Just (tya :-> tyr), Just tya') | tya == tya' -> Just tyr
      _ -> Nothing
    infer' ctx env (Let pat init body) = do
      tyinit <- infer' ctx env init
      Env ctx' <- checkPat pat tyinit
      infer' ((fmap snd ctx') ++ ctx) env body
    infer' ctx env (Pair l r) = do
      l' <- infer' ctx env l
      r' <- infer' ctx env r
      return $ l' :* r'
    infer' ctx env (Fst p) = case infer' ctx env p of
      Just (lty :* _) -> Just lty
      _ -> Nothing
    infer' ctx env (Snd p) = case infer' ctx env p of
      Just (_ :* rty) -> Just rty
      _ -> Nothing
    infer' ctx env Zero = Just Nat
    infer' ctx env (Succ t) = do
      Nat <- infer' ctx env t
      return Nat
    infer' ctx env (Pred t) = do
      Nat <- infer' ctx env t
      return Nat
    infer' ctx env (IsZero t) = do
      Nat <- infer' ctx env t
      return Boo
    infer' ctx env (Fix t) = do
      (l :-> r) <- infer' ctx env t
      guard $ l == r
      return l
    infer' ctx env (Inl t ty) = do
      ty' <- infer' ctx env t
      return $ ty' :+ ty
    infer' ctx env (Inr ty t) = do
      ty' <- infer' ctx env t
      return $ ty :+ ty'
    infer' ctx env (Case t sym l r) = do
      (tyl :+ tyr) <- infer' ctx env t
      tyl' <- infer' (tyl : ctx) env l
      tyr' <- infer' (tyr : ctx) env r
      guard $ tyl' == tyr'
      return tyl'

infer0 :: Term -> Maybe Type
infer0 = infer $ Env []

one = Succ Zero

two = Succ one

three = Succ two

four = Succ three

five = Succ four

six = Succ five

seven = Succ six

eight = Succ seven

nine = Succ eight

ten = Succ nine

plus_ =
  Lmb "f" (Nat :-> Nat :-> Nat) $
    Lmb "m" Nat $
      Lmb "n" Nat $
        If
          (IsZero $ Idx 1)
          (Idx 0)
          (Succ $ Idx 2 :@: Pred (Idx 1) :@: Idx 0)

plus = Fix plus_

minus_ =
  Lmb "f" (Nat :-> Nat :-> Nat) $
    Lmb "m" Nat $
      Lmb "n" Nat $
        If
          (IsZero $ Idx 0)
          (Idx 1)
          (Pred $ Idx 2 :@: Idx 1 :@: Pred (Idx 0))

minus = Fix minus_

eq_ =
  Lmb "f" (Nat :-> Nat :-> Boo) $
    Lmb "m" Nat $
      Lmb "n" Nat $
        If
          (IsZero $ Idx 1)
          (IsZero $ Idx 0)
          ( If
              (IsZero $ Idx 0)
              (IsZero $ Idx 1)
              (Idx 2 :@: Pred (Idx 1) :@: Pred (Idx 0))
          )

eq = Fix eq_

mult_ =
  Lmb "f" (Nat :-> Nat :-> Nat) $
    Lmb "m" Nat $
      Lmb "n" Nat $
        If
          (IsZero $ Idx 1)
          Zero
          (plus :@: Idx 0 :@: (Idx 2 :@: Pred (Idx 1) :@: Idx 0))

mult = Fix mult_

power_ =
  Lmb "f" (Nat :-> Nat :-> Nat) $
    Lmb "m" Nat $
      Lmb "n" Nat $
        If
          (IsZero $ Idx 0)
          one
          (mult :@: Idx 1 :@: (Idx 2 :@: Idx 1 :@: Pred (Idx 0)))

power = Fix power_
