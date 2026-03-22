import Control.Monad (MonadPlus (mzero), forM, guard)
import Data.Maybe (mapMaybe)

type Symb = String

infix 1 <:
infixl 4 :@:
infixr 3 :->
infixl 4 \/
infix 5 /\

data Type
  = Boo
  | Type :-> Type
  | TRcd [(Symb, Type)]
  | Top
  deriving (Read, Show, Eq)

data Pat
  = PVar Symb
  | PRcd [(Symb, Pat)]
  deriving (Read, Show, Eq)

data Term
  = Fls
  | Tru
  | If Term Term Term
  | Idx Int
  | Term :@: Term
  | Lmb Symb Type Term
  | Let Pat Term Term
  | Rcd [(Symb, Term)]
  | Prj Symb Term
  deriving (Read, Show)

instance Eq Term where
  Fls == Fls = True
  Tru == Tru = True
  If b u w == If b1 u1 w1 = b == b1 && u == u1 && w == w1
  Idx m == Idx m1 = m == m1
  (u :@: w) == (u1 :@: w1) = u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1 = t == t1 && u == u1
  Let p u w == Let p1 u1 w1 = p == p1 && u == u1 && w == w1
  Rcd xs == Rcd xs1 = xs == xs1
  Prj l u == Prj l1 u1 = l == l1 && u == u1
  _ == _ = False

newtype Env = Env [(Symb, Type)]
  deriving (Read, Show, Eq)

------------------------------------

(<:) :: Type -> Type -> Bool
_ <: Top = True
(ll :-> lr) <: (rl :-> rr) = (rl <: ll) && (lr <: rr)
(TRcd lfs) <: (TRcd rfs) = all checkField rfs
  where
    checkField (rf, rty) = case lookup rf lfs of
      Nothing -> False
      Just lty -> lty <: rty
l <: r = l == r

(\/) :: Type -> Type -> Type
(ll :-> lr) \/ (rl :-> rr) = case (ll /\ rl) of
  Nothing -> Top
  Just l -> l :-> (lr \/ rr)
(TRcd lfs) \/ (TRcd rfs) = TRcd $ mapMaybe unionField lfs
  where
    unionField (f, lty) = case lookup f rfs of
      Nothing -> Nothing
      Just rty -> Just $ (f, lty \/ rty)
l \/ r
  | l == r = l
  | otherwise = Top

(/\) :: Type -> Type -> Maybe Type
(ll :-> lr) /\ (rl :-> rr) = case lr /\ rr of
  Nothing -> Nothing
  Just r -> Just $ (ll \/ rl) :-> r
(TRcd lfs) /\ (TRcd rfs) = do
  ltys <- forM lfs interField
  let rtys = mapMaybe addField rfs
  return $ TRcd $ ltys ++ rtys
  where
    interField (f, lty) = case lookup f rfs of
      Nothing -> Just (f, lty)
      Just rty -> case lty /\ rty of
        Nothing -> Nothing
        Just ty -> Just (f, ty)
    addField (f, rty) = case lookup f lfs of
      Nothing -> Just (f, rty)
      Just _ -> Nothing
Top /\ r = Just r
l /\ Top = Just l
l /\ r
  | l == r = Just r
  | otherwise = Nothing

countBinds :: Pat -> Int
countBinds (PVar _) = 1
countBinds (PRcd fs) = sum $ fmap (countBinds . snd) fs

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
    shift' val base (Rcd fs) = Rcd $ fmap (\(f, t) -> (f, shift' val base t)) fs
    shift' val base (Prj f t) = Prj f $ shift' val base t

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
substDB j q (Rcd fs) = Rcd $ fmap (\(f, t) -> (f, substDB j q t)) fs
substDB j q (Prj f t) = Prj f $ substDB j q t

isValue :: Term -> Bool
isValue (Lmb _ _ _) = True
isValue Fls = True
isValue Tru = True
isValue (Rcd fs) = all (isValue . snd) fs
isValue _ = False

match :: Pat -> Term -> Maybe [(Symb, Term)]
match (PVar sym) t = do
  guard $ isValue t
  return [(sym, t)]
match (PRcd ps) (Rcd fs) = do
  matchFields ps fs
  where
    matchFields [] fs = Just []
    matchFields ((fp, p) : ps) fs = do
      t <- lookup fp fs
      m <- match p t
      ts <- matchFields ps fs
      return $ m ++ ts
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
oneStep (Rcd fs) = case oneStepRec fs of
  Nothing -> Nothing
  Just fs' -> Just $ Rcd fs'
  where
    oneStepRec [] = Nothing
    oneStepRec ((f, t) : fs) =
      if isValue t
        then case oneStepRec fs of
          Nothing -> Nothing
          Just fs' -> Just $ (f, t) : fs'
        else case oneStep t of
          Nothing -> Nothing
          Just t' -> Just $ (f, t') : fs
oneStep (Prj f r@(Rcd fs)) =
  if isValue r
    then lookup f fs
    else case oneStep r of
      Nothing -> Nothing
      Just r' -> Just $ Prj f r'
oneStep (Prj f t) = case oneStep t of
  Nothing -> Nothing
  Just t' -> Just $ Prj f t'
oneStep _ = Nothing

whnf :: Term -> Term
whnf t =
  case oneStep t of
    Nothing -> t
    Just t' -> whnf t'

checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar sym) ty = Just $ Env [(sym, ty)]
checkPat (PRcd ps) (TRcd fs) = checkPatRec ps fs
  where
    checkPatRec [] fs = Just $ Env []
    checkPatRec ((fp, p) : ps) fs = do
      ty <- lookup fp fs
      (Env env) <- checkPat p ty
      (Env env') <- checkPatRec ps fs
      return $ Env $ env' ++ env
checkPat _ _ = Nothing

infer :: Env -> Term -> Maybe Type
infer = infer' []
  where
    infer' :: [Type] -> Env -> Term -> Maybe Type
    infer' ctx env Tru = Just Boo
    infer' ctx env Fls = Just Boo
    infer' ctx env (If c t e) = case (infer' ctx env c, infer' ctx env t, infer' ctx env e) of
      (Just Boo, Just tyl, Just tye) -> Just $ tyl \/ tye
      _ -> Nothing
    infer' ctx (Env env) (Idx i) =
      if i >= length ctx
        then Just $ snd $ env !! (i - length ctx)
        else Just $ ctx !! i
    infer' ctx env (Lmb v ty b) = case infer' (ty : ctx) env b of
      Nothing -> Nothing
      Just tyb -> Just $ ty :-> tyb
    infer' ctx env (l :@: r) = case (infer' ctx env l, infer' ctx env r) of
      (Just (tya :-> tyr), Just tya') | tya' <: tya -> Just tyr
      _ -> Nothing
    infer' ctx env (Let pat init body) = do
      tyinit <- infer' ctx env init
      Env ctx' <- checkPat pat tyinit
      infer' ((fmap snd ctx') ++ ctx) env body
    infer' ctx env (Rcd fs) = do
      ftys <- forM fs inferRec
      return $ TRcd ftys
      where
        inferRec (f, t) = do
          ty <- infer' ctx env t
          return (f, ty)
    infer' ctx env (Prj f t) = do
      ty <- infer' ctx env t
      case ty of
        (TRcd fs) -> lookup f fs
        _ -> mzero

infer0 :: Term -> Maybe Type
infer0 = infer $ Env []

-----------------------------------------------------------------

type1 = TRcd [("la",Boo),("lb",Boo :-> Boo)]
type2 = TRcd [("lb",Boo :-> Boo), ("lc",Boo :-> Boo :-> Boo)]
body1 = Rcd [("lb",Prj "lb" (Idx 0)),("lc",Lmb "x" Boo $ Prj "lb" (Idx 1))]
body2 = Rcd [("lb",Prj "lb" (Idx 0)),("la",Prj "lb" (Idx 0) :@: Tru)]
func1 = Lmb "x" type1 body1
func2 = Lmb "y" type2 body2
