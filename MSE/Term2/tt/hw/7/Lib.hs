import Control.Monad (guard)
type Symb = String 

infixl 4 :@:, :@>
infixr 3 :->
infix 1 ||-

data Type = TIdx Int
          | Type :-> Type
          | ForAll Symb Type
          | Exists Symb Type -- экзистенциальный тип, Symb - справочное имя связываемой переменной
    deriving (Read,Show,Ord)

instance Eq Type where
  TIdx n1     == TIdx n2     = n1 == n2
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ t1 == ForAll _ t2 = t1 == t2
  Exists _ t1 == Exists _ t2 = t1 == t2
  _           == _           = False

data Decl = VDecl Symb Type
          | TDecl Symb
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
          | As (Type,Term) Type       -- упаковка типа-свидетеля и терма в экзистенциальный тип
          | Let (Symb,Symb) Term Term -- распаковка пакета, имена типа и терма в паре - справочные
    deriving (Read,Show,Ord)

instance Eq Term where
  Idx n1        == Idx n2        = n1 == n2
  (u1 :@: u3)   == (u2 :@: u4)   = u1 == u2 && u3 == u4
  (u1 :@> t3)   == (u2 :@> t4)   = u1 == u2 && t3 == t4
  Lmb d1 u3     == Lmb d2 u4     = d1 == d2 && u3 == u4
  As (t1,u3) t5 == As (t2,u4) t6 = t1 == t2 && u3 == u4 && t5 == t6
  Let _ u1 u3   == Let _ u2 u4   = u1 == u2 && u3 == u4
  _             == _             = False

lV :: Symb -> Type -> Term -> Term
lV v = Lmb . VDecl v

lT :: Symb -> Term -> Term
lT = Lmb . TDecl
------------------------------------


validTy :: Env -> Type -> Bool
validTy env (l :-> r) = validTy env l && validTy env r
validTy env (ForAll s ty) = validTy (TDecl s : env) ty
validTy env (Exists s ty) = validTy (TDecl s : env) ty
validTy env (TIdx n) =
  if n < 0 || n >= length env
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
shiftT' val base (Exists s ty) = Exists s $ shiftT' val (base + 1) ty

shiftT :: Int -> Type -> Type
shiftT val ty = shiftT' val 0 ty

substTT :: Int -> Type -> Type -> Type
substTT j sigma (TIdx n)
  | n == j = sigma
  | otherwise = TIdx n
substTT j sigma (l :-> r) = substTT j sigma l :-> substTT j sigma r
substTT j sigma (ForAll s tau) = ForAll s $ substTT (j + 1) (shiftT 1 sigma) tau
substTT j sigma (Exists s tau) = Exists s $ substTT (j + 1) (shiftT 1 sigma) tau

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
    infer' env (As (ty, v) ety) = do
      (Exists _ ety') <- pure ety
      vty <- infer' env v
      guard $ shiftT (-1) (substTT 0 (shiftT 1 ty) ety') == vty
      return ety
    infer' env (Let (sty, sv) v b) = do
      (Exists _ ety') <- infer' env v
      ty <- infer' (VDecl sv ety' : TDecl sty : env) b
      let ty' = shiftT (-2) ty
      guard $ validTy env ty'
      return ty'

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
    shiftV' val base (As (ty, t) asTy) = As (shiftT' val base ty, shiftV' val base t) $ shiftT' val base asTy
    shiftV' val base (Let ss t tb) = Let ss (shiftV' val base t) $ shiftV' val (base + 2) tb

substVV :: Int -> Term -> Term -> Term
substVV j s (Idx n)
  | n == j = s
  | otherwise = Idx n
substVV j s (l :@: r) = substVV j s l :@: substVV j s r
substVV j s (l :@> t) = substVV j s l :@> t
substVV j s (Lmb decl t) = Lmb decl $ substVV (j + 1) (shiftV 1 s) t
substVV j s (As (ty, t) asTy) = As (ty, substVV j s t) asTy
substVV j s (Let ss t tb) = Let ss (substVV j s t) $ substVV (j + 2) (shiftV 2 s) tb

substTV :: Int -> Type -> Term -> Term
substTV i tau (Idx n) = Idx n
substTV i tau (l :@: r) = substTV i tau l :@: substTV i tau r
substTV i tau (l :@> r) = substTV i tau l :@> substTT i tau r
substTV i tau (Lmb (TDecl s) t) = Lmb (TDecl s) $ substTV (i + 1) (shiftT 1 tau) t
substTV i tau (Lmb (VDecl s st) t) = Lmb (VDecl s $ substTT i tau st) $ substTV (i + 1) (shiftT 1 tau) t
substTV i tau (As (ty, t) asTy) = As (substTT i tau ty, substTV i tau t) $ substTT i tau asTy
substTV i tau (Let ss t b) = Let ss (substTV i tau t) $ substTV (i + 2) (shiftT 2 tau) b

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
    oneStep' env (As (ty, v) ety) = case oneStep v of
        Just v' -> Just $ As (ty, v') ety
        Nothing -> Nothing
    oneStep' env (Let ss t tb) = case oneStep t of
        Just t' -> Just $ Let ss t' tb
        Nothing -> case t of
            (As (ty, term) _) ->
                let tb' = shiftV (-1) $ substVV 0 (shiftV 1 term) tb
                    tb'' = shiftV (-1) $ substTV 0 (shiftT 1 ty) tb'
                in Just tb''
            _ -> Nothing
    oneStep' _ _ = Nothing

nf :: Term -> Term
nf t =
  case oneStep t of
    Nothing -> t
    Just t' -> nf t'

--------------------------------------------------------

cKF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 1
cKastF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 0
tArr  = TIdx 0 :-> TIdx 0

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
suc    = lV "n" natT $ lT "a" $ lV "s" tArr $ lV "z" (TIdx 1) $ Idx 1 :@: (Idx 3 :@> TIdx 2 :@: Idx 1 :@: Idx 0)

plus = lV "m" natT $ lV "n" natT $ lT "c" $ lV "s" (TIdx 0 :-> TIdx 0) $ lV "z" (TIdx 1) $ Idx 4 :@> TIdx 2 :@: Idx 1 :@: (Idx 3 :@> TIdx 2 :@: Idx 1 :@: Idx 0)
mult   = lV "n" natT $ lV "m" natT $ (Idx 1) :@> natT :@: (plus :@: Idx 0) :@: zero

pF = lT "sigma" $ lT "tau" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ 
       lT "a" $ lV "f" (TIdx 4 :-> TIdx 3 :-> TIdx 0) $ Idx 0 :@: Idx 3 :@: Idx 2
pFT = ForAll "sigma" $ ForAll "tau" $ TIdx 1 :-> TIdx 0 :-> 
       (ForAll "a" $ (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 0)
pFT' sigma tau = ForAll "a" $ (shiftT 1 sigma :-> shiftT 1 tau :-> TIdx 0) :-> TIdx 0
pT = ForAll "a" $ (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 0
fstP = lT "sigma" $ lT "tau" $ lV "p" pT $ Idx 0 :@> TIdx 2 :@: (cKF    :@> TIdx 2 :@> TIdx 1)
sndP = lT "sigma" $ lT "tau" $ lV "p" pT $ Idx 0 :@> TIdx 1 :@: (cKastF :@> TIdx 2 :@> TIdx 1)

xz = lT "a" $ lV "x" (TIdx 0) $ pF :@> TIdx 1 :@> natT :@: Idx 0 :@: zero
fs = lT "a" $ lV "f" (TIdx 0 :-> natT :-> TIdx 0) $ lV "p" (pFT' (TIdx 1) natT) $
    pF :@> TIdx 2 :@> natT :@: (Idx 1 :@: (fstP :@> TIdx 2 :@> natT :@: Idx 0) :@: (sndP :@> TIdx 2 :@> natT :@: Idx 0))
        :@: (suc :@: (sndP :@> TIdx 2 :@> natT :@: Idx 0))
rec = lT "a" $ lV "m" natT $ lV "f" (TIdx 1 :-> natT :-> TIdx 1) $ lV "x" (TIdx 2) $
    fstP :@> TIdx 3 :@> natT :@: (Idx 2 :@> (pFT' (TIdx 3) natT) :@: (fs :@> TIdx 3 :@: Idx 1) :@: (xz :@> TIdx 3 :@: Idx 0))

pre = lV "n" natT $ rec :@> natT :@: Idx 0 :@: preFun :@: preIni
preFun = lV "_" natT $ lV "n" natT $ Idx 0
preIni = zero

fac = lV "n" natT $ rec :@> natT :@: Idx 0 :@: facFun :@: facIni
facFun = lV "n" natT $ lV "m" natT $ mult :@: Idx 1 :@: (suc :@: Idx 0)
facIni = one

--------------------------------------------------------------------------------
tstP = pF :@> natT :@> (natT :-> natT) :@: two :@: (plus :@: three)
tstPT = ForAll "a" $ (natT :-> (natT :-> natT) :-> TIdx 0) :-> TIdx 0

tstPTEx = Exists "b" $ ForAll "a" $ (TIdx 1 :-> (TIdx 1 :-> natT) :-> TIdx 0) :-> TIdx 0

packedP = (natT,tstP) `As` tstPTEx

test = Let ("gamma","p") packedP testBody where 
  testBody = snd_ :@: fst_
  fst_ = Idx 0 :@> TIdx 1            :@: (cKF    :@> TIdx 1 :@> (TIdx 1 :-> natT))
  snd_ = Idx 0 :@> (TIdx 1 :-> natT) :@: (cKastF :@> TIdx 1 :@> (TIdx 1 :-> natT))

test1 = Let ("gamma","p") packedP testBody where 
  testBody = snd_ :@: seven   -- тип seven - это natT, в snd_ ожидается "gamma"
  snd_ = Idx 0 :@> (TIdx 1 :-> natT) :@: (cKastF :@> TIdx 1 :@> (TIdx 1 :-> natT))

test2 = Let ("gamma","p") packedP testBody where 
  testBody = fst_             -- тип "gamma" локален и не может быть доступен извне 
  fst_ = Idx 0 :@> TIdx 1      

test80 = lT "a" $ (TIdx 0, lV "x" (TIdx 0) $ Idx 0) `As` (Exists "b" $ TIdx 0 :-> TIdx 1)

---------------------------------------------------------------------------------------------

tNat = tArr :-> tArr

tNatF = ForAll "a" tNat

plusF = lV "m" tNatF $ lV "n" tNatF $ lT "c" $ lV "s" (TIdx 0 :-> TIdx 0) $ lV "z" (TIdx 1) $ Idx 4 :@> TIdx 2 :@: Idx 1 :@: (Idx 3 :@> TIdx 2 :@: Idx 1 :@: Idx 0)

boolT = ForAll "a" $ TIdx 0 :-> TIdx 0 :-> TIdx 0

fls = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 0

ifThenElse = lT "a" $ lV "v" boolT $ lV "x" (TIdx 1) $ lV "y" (TIdx 2) $ Idx 2 :@> TIdx 3 :@: Idx 1 :@: Idx 0

fst_ = Idx 0 :@> TIdx 1 :@: (cKF :@> TIdx 1 :@> (TIdx 1 :-> natT))

snd_ = Idx 0 :@> (TIdx 1 :-> natT) :@: (cKastF :@> TIdx 1 :@> (TIdx 1 :-> natT))

tstP' = pF :@> boolT :@> (boolT :-> natT) :@: fls :@: (lV "x" boolT $ ifThenElse :@> natT :@: Idx 0 :@: three :@: four)

packedP' = (boolT, tstP') `As` tstPTEx

test'' = Let ("gamma", "p") packedP' testBody where testBody = plusF :@: (snd_ :@: fst_) :@: Idx 2
