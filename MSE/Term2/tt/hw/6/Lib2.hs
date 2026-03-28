import Control.Monad (guard)
type Symb = String 

infixl 4 :@:, :@>
infixr 3 :->
infix 1 ||-

data Type = TIdx Int         -- типовой атом как индекс Де Брауна
          | Type :-> Type    -- стрелочный тип
          | ForAll Symb Type -- полиморфный тип, Symb - справочное имя связываемой переменной
    deriving (Read,Show,Ord)

instance Eq Type where
  TIdx n1     == TIdx n2     = n1 == n2
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ t1 == ForAll _ t2 = t1 == t2
  _           == _           = False

-- Объявление либо переменная, либо тип
data Decl = VDecl Symb Type --  объявление термовой переменной с ее типом, Symb - справочное имя этой переменной
          | TDecl Symb      --  объявление типовой переменной, Symb - справочное имя этой переменной
    deriving (Read,Show,Ord)

instance Eq Decl where
  VDecl _ t1 == VDecl _ t2 = t1 == t2
  TDecl _    == TDecl _    = True
  _          == _          = False

type Env = [Decl]

data Term = Idx Int
          | Term :@: Term
          | Term :@> Type
          | Lmb Decl Term
    deriving (Read,Show,Eq,Ord)

lV :: Symb -> Type -> Term -> Term
lV v = Lmb . VDecl v

lT :: Symb -> Term -> Term
lT = Lmb . TDecl
------------------------------------


validTy :: Env -> Type -> Bool
validTy env (l :-> r) = validTy env l && validTy env r
validTy env (ForAll s ty) = validTy (TDecl s : env) ty
validTy env (TIdx n) =
  if n >= length env
    then False
    else case env !! n of
      (VDecl _ _) -> False
      (TDecl _) -> True

validEnv :: Env -> Bool
validEnv env = validEnv' [] env
  where
    validEnv' env (e@(TDecl _) : env') = validEnv' (e : env) env'
    validEnv' env (e@(VDecl _ ty) : env') = validTy env' ty && validEnv' (e : env) env'
    validEnv' _ _ = True

(||-) :: Env -> Type -> Bool
e ||- t = validTy e t

shiftT' :: Int -> Int -> Type -> Type
shiftT' val base (TIdx n)
  | n < base = TIdx n
  | otherwise = TIdx $ n + val
shiftT' val base (l :-> r) = shiftT' val base l :-> shiftT' val base r
shiftT' val base (ForAll s ty) = ForAll s $ shiftT' val (base + 1) ty

shiftT :: Int -> Type -> Type
shiftT val ty = shiftT' val 0 ty

substTT :: Int -> Type -> Type -> Type
substTT j sigma (TIdx n)
  | n == j = sigma
  | otherwise = TIdx n
substTT j sigma (l :-> r) = substTT j sigma l :-> substTT j sigma r
substTT j sigma (ForAll s tau) = ForAll s $ substTT (j + 1) (shiftT 1 sigma) tau

infer :: Env -> Term -> Maybe Type
infer env t = if validEnv env then infer' env t else Nothing
  where
    infer' :: Env -> Term -> Maybe Type
    infer' env (Idx n) = do
      guard $ n < length env
      (VDecl _ ty) <- pure $ env !! n
      return $ shiftT (n + 1) ty
    infer' env (l :@: r) = do
      (tya :-> tyr) <- infer env l
      tya' <- infer env r
      guard $ tya == tya'
      return tyr
    infer' env (l :@> ty) = do
      (ForAll s tya) <- infer env l
      return $ shiftT (-1) $ substTT 0 (shiftT 1 ty) tya
    infer' env (Lmb (TDecl s) t) = do
      ty <- infer (TDecl s : env) t
      return $ ForAll s ty
    infer' env (Lmb (VDecl s tyv) t) = do
      ty <- infer (VDecl s tyv : env) t
      return $ tyv :-> (shiftT (-1) ty)

infer0 :: Term -> Maybe Type
infer0 = infer []

shiftV :: Int -> Term -> Term
shiftV val = shiftV' val 0
  where
    shiftV' :: Int -> Int -> Term -> Term
    shiftV' val base (Idx n)
      | n < base = Idx n
      | otherwise = Idx $ n + val
    shiftV' val base (l :@: r) = shiftV' val base l :@: shiftV' val base r
    shiftV' val base (l :@> r) = shiftV' val base l :@> shiftT' val base r
    shiftV' val base (Lmb (TDecl s) t) = Lmb (TDecl s) $ shiftV' val (base + 1) t
    shiftV' val base (Lmb (VDecl s st) t) = Lmb (VDecl s $ shiftT' val base st) $ shiftV' val (base + 1) t

substVV :: Int -> Term -> Term -> Term
substVV j s (Idx n)
  | n == j = s
  | otherwise = Idx n
substVV j s (l :@: r) = substVV j s l :@: substVV j s r
substVV j s (l :@> t) = substVV j s l :@> t
substVV j s (Lmb decl t) = Lmb decl $ substVV (j + 1) (shiftV 1 s) t

substTV :: Int -> Type -> Term -> Term
substTV i tau (Idx n) = Idx n
substTV i tau (l :@: r) = substTV i tau l :@: substTV i tau r
substTV i tau (l :@> r) = substTV i tau l :@> substTT i tau r
substTV i tau (Lmb (TDecl s) t) = Lmb (TDecl s) $ substTV (i + 1) (shiftT 1 tau) t
substTV i tau (Lmb (VDecl s st) t) = Lmb (VDecl s $ substTT i tau st) $ substTV (i + 1) (shiftT 1 tau) t

oneStep :: Term -> Maybe Term
oneStep t = oneStep' [] t
  where
    oneStep' :: Env -> Term -> Maybe Term
    oneStep' env t@((Lmb decl@(VDecl _ _) b) :@: a) = do
      return $ shiftV (-1) $ substVV 0 (shiftV 1 a) b
    oneStep' env t@((Lmb decl@(TDecl _) b) :@> a) = do
      return $ shiftV (-1) $ substTV 0 (shiftT 1 a) b
    oneStep' env (Lmb decl b) = do
      b' <- oneStep' (decl : env) b
      return $ Lmb decl b'
    oneStep' env (l :@: r) = case oneStep l of
        Just l' -> Just $ l' :@: r
        Nothing -> case oneStep r of
            Just r' -> Just $ l :@: r'
            Nothing -> Nothing
    oneStep' env (l :@> r) = do
      l' <- oneStep' env l
      return $ l' :@> r
    oneStep' _ _ = Nothing

nf :: Term -> Term
nf t =
  case oneStep t of
    Nothing -> t
    Just t' -> nf t'

--------------------------------------------

botT = ForAll "a" (TIdx 0)
topT = ForAll "a" (TIdx 0 :-> TIdx 0)
boolT = ForAll "a" (TIdx 0 :-> TIdx 0 :-> TIdx 0)

answer11 = lV "f" topT $ Idx 0 :@> (topT :-> topT) :@: (Idx 0 :@> topT) :@: Idx 0
answer12 = lV "f" topT $ Idx 0 :@> topT :@: Idx 0 :@> topT :@: Idx 0

answer21 = lV "f" boolT $ Idx 0 :@> boolT :@: Idx 0 :@: Idx 0
answer22 = lV "f" boolT $ Idx 0 :@> boolT :@: (lT "a" $ Idx 1 :@> TIdx 0) :@: (lT "a" $ Idx 1 :@> TIdx 0)

answer31 = lV "f" botT $ Idx 0 :@> (botT :-> botT) :@: Idx 0 :@> (botT :-> botT) :@: Idx 0
answer32 = lV "f" botT $ Idx 0 :@> (botT :-> botT :-> botT) :@: Idx 0 :@: Idx 0

answer41 = lV "f" topT $ Idx 0 :@> topT :@: Idx 0 :@> topT :@: (Idx 0 :@> topT :@: Idx 0)
answer42 = lV "f" topT $ Idx 0 :@> (topT :-> topT) :@: (Idx 0 :@> topT) :@: (Idx 0 :@> topT :@: Idx 0)

answer51 = lV "f" botT $ Idx 0 :@> (botT :-> botT) :@: Idx 0 :@> (botT :-> botT) :@: (Idx 0 :@> (botT :-> botT) :@: Idx 0)
answer52 = lV "f" botT $ Idx 0 :@> (botT :-> botT :-> botT) :@: Idx 0 :@: (Idx 0 :@> (botT :-> botT) :@: Idx 0)

answer61 = lV "f" boolT $ Idx 0 :@> boolT :@: Idx 0 
answer62 = lV "f" boolT $ Idx 0 :@> boolT :@: (lT "a" $ Idx 1 :@> TIdx 0)

answer7 = lV "s" (ForAll "a" $ TIdx 0 :-> TIdx 1 :-> TIdx 0) $ lT "a" $ lV "z" (TIdx 0) $ Idx 2 :@> (TIdx 3 :-> TIdx 1) :@: (Idx 2 :@> (TIdx 1) :@: Idx 0)

answer8 = lV "s" (ForAll "a" $ TIdx 0 :-> TIdx 2 :-> TIdx 1 :-> TIdx 0) $ lT "a" $ lV "z" (TIdx 0) $ Idx 2 :@> (TIdx 4 :-> TIdx 3 :-> TIdx 1) :@: (Idx 2 :@> (TIdx 1) :@: Idx 0)
