import Control.Applicative ((<|>))
import Control.Monad (guard, mzero)
import Data.Maybe (isJust)

type Symb = String

infixl 4 :@:

infixr 3 >-> -- теперь просто функция

data Expr
  = Idx Int
  | Ast
  | Box
  | Expr :@: Expr
  | Lmb Decl Expr
  | Pi Decl Expr -- расширенный функциональный тип
  deriving (Read, Show, Eq, Ord)

data Decl = EDecl Symb Expr
  deriving (Read, Show, Ord)

instance Eq Decl where
  EDecl _ t1 == EDecl _ t2 = t1 == t2

type Env = [Decl]

lE, pE :: Symb -> Expr -> Expr -> Expr
lE v = Lmb . EDecl v
pE v = Pi . EDecl v

(>->) :: Expr -> Expr -> Expr
a >-> b = pE "_" a (shift 1 b)

----------------------

validEnv :: Env -> Bool
validEnv [] = True
validEnv (EDecl sy ty : env) = maybe False astOrBox (infer' env ty) && validEnv env

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
    shift' val base (Pi (EDecl s ty) expr) = Pi (EDecl s $ shift' val base ty) $ shift' val (base + 1) expr

subst :: Int -> Expr -> Expr -> Expr
subst j s (Idx n)
  | n == j = s
  | otherwise = Idx n
subst _ _ Ast = Ast
subst _ _ Box = Box
subst j s (l :@: r) = subst j s l :@: subst j s r
subst j s (Lmb (EDecl sym ty) expr) = Lmb (EDecl sym $ subst j s ty) $ subst (j + 1) (shift 1 s) expr
subst j s (Pi (EDecl sym ty) expr) = Pi (EDecl sym $ subst j s ty) $ subst (j + 1) (shift 1 s) expr

astOrBox :: Expr -> Bool
astOrBox Ast = True
astOrBox Box = True
astOrBox _ = False

infer' :: Env -> Expr -> Maybe Expr
infer' _ Ast = Just Box
-- infer' (EDecl _ ty : env) (Idx 0) = do
--   True <- astOrBox <$> infer' env ty
--   return $ shift 1 $ ty
-- infer' (EDecl _ ty : env) (Idx n) = do
--   True <- astOrBox <$> infer' env ty
--   shift 1 <$> (infer' env $ Idx $ n - 1)
infer' env (Idx n) = do
  guard $ n < length env
  (EDecl _ ty) <- pure $ env !! n
  return $ shift (n + 1) ty
infer' env (Pi (EDecl sym ty) expr) = do
  Ast <- infer' env ty
  ki <- infer' ((EDecl sym ty) : env) expr
  guard $ astOrBox ki
  return ki
infer' env (l :@: r) = do
  (Pi (EDecl sy argTy) ty) <- infer' env l
  argTy' <- infer' env r
  guard $ nf argTy == nf argTy'
  return $ shift (-1) $ subst 0 (shift 1 r) ty
infer' env (Lmb decl@(EDecl s argTy) expr) = do
  Ast <- infer' env argTy
  ty <- infer' (decl : env) expr
  return $ Pi decl ty
infer' _ _ = Nothing

infer :: Env -> Expr -> Maybe Expr
infer env expr = do
  guard $ validEnv env
  infer' env expr

infer0 :: Expr -> Maybe Expr
infer0 = infer' []

oneStep :: Expr -> Maybe Expr
oneStep t@((Lmb decl b) :@: a) = do
  return $ shift (-1) $ subst 0 (shift 1 a) b
oneStep (Lmb decl@(EDecl s ty) b) =
  let tyRed = do
        ty' <- oneStep ty
        return $ Lmb (EDecl s ty') b
      bodyRed = do
        b' <- oneStep b
        return $ Lmb decl b'
   in tyRed <|> bodyRed
oneStep (Pi decl@(EDecl sym ty) expr) = do
  let tyRed = do
        ty' <- oneStep ty
        return $ Pi (EDecl sym ty') expr
      exprRed = do
        expr' <- oneStep expr
        return $ Pi (EDecl sym ty) expr'
   in tyRed <|> exprRed
oneStep (l :@: r) = do
  let lRed = do
        l' <- oneStep l
        return $ l' :@: r
      rRed = do
        r' <- oneStep r
        return $ l :@: r'
   in lRed <|> rRed
oneStep _ = Nothing

nf :: Expr -> Expr
nf t =
  case oneStep t of
    Nothing -> t
    Just t' -> nf t'

-------------------------------------------------------------

-- natPref i = lE "s" (Idx i >-> Idx i) . lE "z" (Idx $ i+1)
-- cIDB = lE "x" (Idx 0) (Idx 0)
-- twoi i = natPref i (Idx 1 :@: (Idx 1 :@: Idx 0))
-- test = oneStep (lE "x" (Idx 0 :@: (cIDB :@: twoi 1)) (cIDB :@: twoi 1)) == Just (lE "x" (Idx 0 :@: twoi 1) (cIDB :@: twoi 1))
