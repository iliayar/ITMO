import Control.Applicative ((<|>))
import Control.Monad (guard, mzero)

type Symb = String

infixl 4 :@:

infixr 3 :->

data Expr
  = Idx Int -- переменная как индекс Де Брауна
  | Ast -- константа, базовый атом для кайндов
  | Box -- константа высшего уровня
  | Expr :@: Expr -- аппликация терма к терму или типа к типу
  | Lmb Decl Expr -- абстракция терма или типа
  | Expr :-> Expr -- стрелочный тип или кайнд
  | ForAll Symb Expr Expr -- полиморфный тип, второй аргумент - кайнд типовой переменной
  deriving (Read, Show, Ord)

instance Eq Expr where
  Idx n1 == Idx n2 = n1 == n2
  Ast == Ast = True
  Box == Box = True
  (u1 :@: u3) == (u2 :@: u4) = u1 == u2 && u3 == u4
  Lmb d1 u3 == Lmb d2 u4 = d1 == d2 && u3 == u4
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ lKi lTy == ForAll _ rKi rTy = lKi == lKi && lTy == rTy
  _ == _ = False

data Decl = EDecl Symb Expr --  объявление биндера с типом/кайндом, Symb - справочное имя переменной
  deriving (Read, Show, Ord)

instance Eq Decl where
  EDecl _ t1 == EDecl _ t2 = t1 == t2

type Env = [Decl]

lE :: Symb -> Expr -> Expr -> Expr
lE v = Lmb . EDecl v

----------------------

shift :: Int -> Expr -> Expr
shift val = shift' val 0
  where
    shift' :: Int -> Int -> Expr -> Expr
    shift' val base (Idx n)
      | n < base = Idx n
      | otherwise = Idx $ n + val
    shift' _ _ Ast = Ast
    shift' _ _ Box = Box
    shift' val base (l :@: r) = shift' val base l :@: shift' val base r
    shift' val base (Lmb (EDecl s ty) expr) = Lmb (EDecl s $ shift' val base ty) $ shift' val (base + 1) expr
    shift' val base (l :-> r) = shift' val base l :-> shift' val base r
    shift' val base (ForAll s ki ty) = ForAll s (shift' val base ki) $ shift' val (base + 1) ty

subst :: Int -> Expr -> Expr -> Expr
subst j s (Idx n)
  | n == j = s
  | otherwise = Idx n
subst _ _ Ast = Ast
subst _ _ Box = Box
subst j s (l :@: r) = subst j s l :@: subst j s r
subst j s (Lmb (EDecl sym ty) expr) = Lmb (EDecl sym $ subst j s ty) $ subst (j + 1) (shift 1 s) expr
subst j s (l :-> r) = subst j s l :-> subst j s r
subst j s (ForAll sym ki ty) = ForAll sym (subst j s ki) $ subst (j + 1) (shift 1 s) ty


astOrBox :: Expr -> Bool
astOrBox Ast = True
astOrBox Box = True
astOrBox _ = False

infer :: Env -> Expr -> Maybe Expr
infer [] Ast = Just Box
infer (EDecl _ ty : env) Ast = do
  True <- astOrBox <$> infer env ty
  shift 1 <$> infer env Ast
infer (EDecl _ ty : env) (Idx 0) = do
  True <- astOrBox <$> infer env ty
  return $ shift 1 $ ty
infer (EDecl _ ty : env) (Idx n) = do
  True <- astOrBox <$> infer env ty
  shift 1 <$> (infer env $ Idx $ n - 1)
infer env (l :-> r) = do
  lTy <- infer env l
  rTy <- infer env r
  guard $ lTy == rTy
  return lTy
infer env (l :@: r) = do
  lTy <- nf <$> infer env l
  case lTy of
    arrL :-> arrR -> do
      rTy <- infer env r
      guard $ nf arrL == nf rTy
      return arrR
    ForAll _ ki ty -> do
      rKi <- infer env r
      guard $ ki == rKi
      return $ shift (-1) $ subst 0 (shift 1 r) ty
    _ -> mzero
infer env (Lmb decl@(EDecl s ty) expr) =
  let abs = do
        exprTy <- infer (decl : env) expr
        True <- astOrBox <$> infer (decl : env) (shift 1 ty :-> exprTy)
        return $ ty :-> shift (-1) exprTy
      tabs = do
        exprTy <- infer (decl : env) expr
        Ast <- infer env $ ForAll s ty exprTy
        return $ ForAll s ty exprTy
   in tabs <|> abs
infer env (ForAll s ki ty) = do
  kiSo <- infer env ki
  guard $ kiSo == Box
  tyKi <- infer (EDecl s ki : env) ty
  guard $ tyKi == Ast
  return Ast
infer _ _ = Nothing

infer0 :: Expr -> Maybe Expr
infer0 = infer []

oneStep :: Expr -> Maybe Expr
oneStep = oneStep' []
  where
    oneStep' :: Env -> Expr -> Maybe Expr
    oneStep' env t@((Lmb decl b) :@: a) = do
      return $ shift (-1) $ subst 0 (shift 1 a) b
    oneStep' env (Lmb decl@(EDecl s ty) b) =
      let tyRed = do
            ty' <- oneStep' env ty
            return $ Lmb (EDecl s ty') b
          tyBody = do
            b' <- oneStep' (decl : env) b
            return $ Lmb decl b'
       in tyRed <|> tyBody
    oneStep' env (l :-> r) = do
      let lRed = do
            l' <- oneStep' env l
            return $ l' :-> r
          rRed = do
            r' <- oneStep' env r
            return $ l :-> r'
       in lRed <|> rRed
    oneStep' env (l :@: r) = do
      let lRed = do
            l' <- oneStep' env l
            return $ l' :@: r
          rRed = do
            r' <- oneStep' env r
            return $ l :@: r'
       in lRed <|> rRed
    oneStep' env (ForAll s ki ty) = do
      ty' <- oneStep' env ty
      return $ ForAll s ki ty'
    oneStep' _ _ = Nothing

nf :: Expr -> Expr
nf t =
  case oneStep t of
    Nothing -> t
    Just t' -> nf t'

twoK = lE "beta" Ast $ (lE "s" (ForAll "alpha" Ast $ Idx 0 :-> Idx 1 :-> Idx 0) $
        lE "alpha" Ast $ lE "z" (Idx 0) $ (Idx 2 :@: (Idx 3 :-> Idx 1) :@: (Idx 2 :@: Idx 1 :@: Idx 0))) 
   :@: (lE "alpha" Ast $ lE "x" (Idx 0) $  lE "y" (Idx 2) $ Idx 1)

two = lE "psi" ((Ast :-> Ast) :-> Ast :-> Ast) $ 
        lE "s" (ForAll "phi" (Ast :-> Ast) $ 
                 (ForAll "alpha" Ast $ Idx 0 :-> Idx 1 :@: Idx 0) :-> (ForAll "alpha" Ast $ Idx 0 :-> Idx 2 :@: Idx 1 :@: Idx 0)) $
          lE "phi" (Ast :-> Ast) $
            lE "z" (ForAll "alpha" Ast $ Idx 0 :-> Idx 1 :@: Idx 0) $ 
              Idx 2 :@: (Idx 3 :@: Idx 1) :@: (Idx 2 :@: Idx 1 :@: Idx 0)
-- целевой тип для удобства
twoType = ForAll "psi" ((Ast :-> Ast) :-> Ast :-> Ast) (t1 :-> t2) where
  t1 = ForAll "phi" (Ast :-> Ast) $ 
    ForAll "a" Ast (Idx 0 :-> (Idx 1 :@: Idx 0)) :-> ForAll "a" Ast (Idx 0 :-> (Idx 2 :@: Idx 1 :@: Idx 0))
  t2 = ForAll "varphi" (Ast :-> Ast) $ 
    ForAll "a" Ast (Idx 0 :-> (Idx 1 :@: Idx 0)) :-> ForAll "a" Ast (Idx 0 :-> (Idx 2 :@: (Idx 2 :@: Idx 1) :@: Idx 0))

two' = lE "phi" (Ast :-> Ast) $
         lE "s" (ForAll "alpha" Ast $ Idx 0 :-> Idx 1 :@: Idx 0) $
           lE "alpha" Ast $
             lE "z" (Idx 0) $
               Idx 2 :@: (Idx 3 :@: Idx 1) :@: (Idx 2 :@: Idx 1 :@: Idx 0)
    
twotwoK = lE "beta" Ast $ 
            two :@: (lE "phi" (Ast :-> Ast) $ lE "alpha" Ast $ Idx 1 :@: (Idx 1 :@: Idx 0)) :@: 
                two' :@: (lE "alpha" Ast $ Idx 1 :-> Idx 0) :@:
                    (lE "alpha" Ast $ lE "x" (Idx 0) $ lE "y" (Idx 2) $ Idx 1)


