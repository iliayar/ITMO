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


-- типовой индекс в типе ссылается на номер объемлющего ForAll
botF = ForAll "a" (TIdx 0)
tArr  = TIdx 0 :-> TIdx 0
topF = ForAll "a" tArr
-- Кодирование самоприменения в System F (примеры из лекции)
sa0 = lV "z" botF $ lT "b" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)
sa1 = lV "z" topF $ lT "b" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)
sa2 = lV "z" topF $ Idx 0 :@> topF :@: Idx 0

-- Комбинатор $I$ (TIdx 0 в cIFopen ссылается в никуда, нужен контекст)
cIFopen = lV "x" (TIdx 0) $ Idx 0  
cIF = lT "a" $ lV "x" (TIdx 0) $ Idx 0

-- Комбинаторы $K$ и $K_\ast$
tK    = TIdx 1 :-> TIdx 0 :-> TIdx 1
tKF = ForAll "a" $ ForAll "b" tK
cKF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 1
tKast = TIdx 1 :-> TIdx 0 :-> TIdx 0
tKastF = ForAll "a" $ ForAll "b" tKast
cKastF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 0

-- Комбинатор $C$ 
tFlip = (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 1 :-> TIdx 2 :-> TIdx 0
tFlipF = ForAll "a" $ ForAll "b" $ ForAll "c" $ tFlip
cFlipF = lT "a" $ lT "b" $ lT "c" $ lV "f" (TIdx 2 :-> TIdx 1 :-> TIdx 0) $ lV "y" (TIdx 2) $ lV "x" (TIdx 4) $ Idx 2 :@: Idx 0 :@: Idx 1

-- Кодирование булевых значений в System F
boolT = ForAll "a" $ TIdx 0 :-> TIdx 0 :-> TIdx 0
fls = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 0
tru = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 1

ifThenElse = lT "a" $ lV "v" boolT $ lV "x" (TIdx 1) $ lV "y" (TIdx 2) $ Idx 2 :@> TIdx 3 :@: Idx 1 :@: Idx 0
notF = lV "v" boolT $ lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 3 :@> TIdx 2 :@: Idx 0 :@: Idx 1

-- Кодирование натуральных чисел в System F
natT = ForAll "a" $ (TIdx 0 :-> TIdx 0) :-> TIdx 0 :-> TIdx 0
natAbs body = lT "a" $ lV "s" (TIdx 0 :-> TIdx 0) $ lV "z" (TIdx 1) body
zero  = natAbs $ Idx 0
one   = natAbs $ Idx 1 :@: Idx 0
two   = natAbs $ Idx 1 :@: (Idx 1 :@: Idx 0)
three = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))
four  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))
five  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))
six   = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))
seven = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))
eight = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))
nine  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))))
ten   = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))))


isZero, suc, plus, mult, power :: Term
isZero = lV "n" natT $ (Idx 0) :@> boolT :@: (cKF :@> boolT :@> boolT :@: fls) :@: tru
suc    = lV "n" natT $ lT "a" $ lV "s" tArr $ lV "z" (TIdx 1) $ Idx 1 :@: (Idx 3 :@> TIdx 2 :@: Idx 1 :@: Idx 0)
plus = lV "m" natT $ lV "n" natT $ lT "c" $ lV "s" (TIdx 0 :-> TIdx 0) $ lV "z" (TIdx 1) $ Idx 4 :@> TIdx 2 :@: Idx 1 :@: (Idx 3 :@> TIdx 2 :@: Idx 1 :@: Idx 0)
mult   = lV "n" natT $ lV "m" natT $ (Idx 1) :@> natT :@: (plus :@: Idx 0) :@: zero
power  = lV "n" natT $ lV "m" natT $ (Idx 0) :@> natT :@: (mult :@: Idx 1) :@: one
