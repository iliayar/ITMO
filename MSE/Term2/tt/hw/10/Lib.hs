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

type Rule = (Expr, Expr)

rulesS, rulesF, rulesO, rulesP, rulesFO, rulesPF, rulesPO, rulesPFO :: [Rule]
rulesS = [(Ast, Ast)]
rulesF = (Box, Ast) : rulesS
rulesO = (Box, Box) : rulesS
rulesP = (Ast, Box) : rulesS
rulesFO = (Box, Ast) : rulesO
rulesPF = (Ast, Box) : rulesF
rulesPO = (Ast, Box) : rulesO
rulesPFO = (Ast, Box) : rulesFO

----------------------

validEnv :: [Rule] -> Env -> Bool
validEnv rules [] = True
validEnv rules (EDecl sy ty : env) = maybe False astOrBox (infer' rules env ty) && validEnv rules env

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

infer' :: [Rule] -> Env -> Expr -> Maybe Expr
infer' _ _ Ast = Just Box
infer' rules env (Idx n) = do
  guard $ n < length env
  (EDecl _ ty) <- pure $ env !! n
  return $ shift (n + 1) ty
infer' rules env (Pi (EDecl sym ty) expr) = do
  s1 <- infer' rules env ty
  s2 <- infer' rules ((EDecl sym ty) : env) expr
  guard $ elem (s1, s2) rules
  return s2
infer' rules env (l :@: r) = do
  (Pi (EDecl sy argTy) ty) <- nf <$> infer' rules env l
  argTy' <- infer' rules env r
  guard $ nf argTy == nf argTy'
  return $ shift (-1) $ subst 0 (shift 1 r) ty
infer' rules env (Lmb decl@(EDecl s argTy) expr) = do
  s1 <- infer' rules env argTy
  ty <- infer' rules (decl : env) expr
  let res = Pi decl ty
  s2 <- infer' rules env res
  return $ res
infer' _ _ _ = Nothing

infer :: [Rule] -> Env -> Expr -> Maybe Expr
infer rules env expr = do
  guard $ validEnv rules env
  infer' rules env expr

infer0 :: [Rule] -> Expr -> Maybe Expr
infer0 rules = infer' rules []

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

tArr = Idx 0 >-> Idx 0

tBool = Idx 0 >-> Idx 0 >-> Idx 0

tNat = tArr >-> tArr

tK = Idx 1 >-> Idx 0 >-> Idx 1

tKast = Idx 1 >-> Idx 0 >-> Idx 0

-- Комбинатор $I$ (Idx 0 в cIFopen ссылается в никуда, нужен контекст)
cIFopen = lE "x" (Idx 0) $ Idx 0

cIF = lE "a" Ast $ lE "x" (Idx 0) $ Idx 0

-- Комбинаторы $K$ и $K_\ast$
tKF = pE "a" Ast $ pE "b" Ast tK

cKF = lE "a" Ast $ lE "b" Ast $ lE "x" (Idx 1) $ lE "y" (Idx 1) $ Idx 1

tKastF = pE "a" Ast $ pE "b" Ast tKast

cKastF = lE "a" Ast $ lE "b" Ast $ lE "x" (Idx 1) $ lE "y" (Idx 1) $ Idx 0

-- Комбинатор $C$
tFlip = (Idx 2 >-> Idx 1 >-> Idx 0) >-> Idx 1 >-> Idx 2 >-> Idx 0

tFlipF = pE "a" Ast $ pE "b" Ast $ pE "c" Ast $ tFlip

cFlipF = lE "a" Ast $ lE "b" Ast $ lE "c" Ast $ lE "f" (Idx 2 >-> Idx 1 >-> Idx 0) $ lE "y" (Idx 2) $ lE "x" (Idx 4) $ Idx 2 :@: Idx 0 :@: Idx 1

-- Кодирование булевых значений в System F
boolT = pE "a" Ast $ Idx 0 >-> Idx 0 >-> Idx 0

fls = lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 0

tru = lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 1

ifThenElse = lE "a" Ast $ lE "v" boolT $ lE "x" (Idx 1) $ lE "y" (Idx 2) $ Idx 2 :@: Idx 3 :@: Idx 1 :@: Idx 0

notF = lE "v" boolT $ lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 3 :@: Idx 2 :@: Idx 0 :@: Idx 1

-- Кодирование самоприменения в System F (примеры из лекции)
botF = pE "a" Ast (Idx 0)

topF = pE "a" Ast tArr

sa0 = lE "z" botF $ lE "b" Ast $ Idx 1 :@: (Idx 0 >-> Idx 0) :@: (Idx 1 :@: Idx 0)

sa1 = lE "z" topF $ lE "b" Ast $ Idx 1 :@: (Idx 0 >-> Idx 0) :@: (Idx 1 :@: Idx 0)

sa2 = lE "z" topF $ Idx 0 :@: topF :@: Idx 0

-- Кодирование натуральных чисел в System F
natT = pE "a" Ast $ (Idx 0 >-> Idx 0) >-> Idx 0 >-> Idx 0

natAbs body = lE "a" Ast $ lE "s" (Idx 0 >-> Idx 0) $ lE "z" (Idx 1) body

zero = natAbs $ Idx 0

one = natAbs $ Idx 1 :@: Idx 0

two = natAbs $ Idx 1 :@: (Idx 1 :@: Idx 0)

three = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))

four = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))

five = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))

six = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))

seven = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))

eight = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))

nine = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))))

ten = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))))

isZeroF = lE "m" natT $ Idx 0 :@: boolT :@: lE "x" boolT fls :@: tru

succF = lE "m" natT $ lE "b" Ast $ lE "s" (Idx 0 >-> Idx 0) $ lE "z" (Idx 1) $ Idx 1 :@: (Idx 3 :@: Idx 2 :@: Idx 1 :@: Idx 0)

-- кодирование вектора в Calculus of Construction
vecT =
  lE "sigma" Ast $
    lE "m" natT $
      pE "phi" (natT >-> Ast) $
        (Idx 0 :@: zero)
          >-> (pE "n" natT $ Idx 3 >-> Idx 1 :@: Idx 0 >-> Idx 1 :@: (succF :@: Idx 0))
          >-> Idx 0
          :@: Idx 1

nil =
  lE "sigma" Ast $
    lE "phi" (natT >-> Ast) $
      lE "z" (Idx 0 :@: zero) $
        lE "c" (pE "n" natT $ Idx 3 >-> Idx 2 :@: Idx 0 >-> Idx 2 :@: (succF :@: Idx 0)) $
          (Idx 1)

nilT =
  nf $
    pE "sigma" Ast $
      vecT :@: Idx 0 :@: zero

cons =
  lE "sigma" Ast $
    lE "n" natT $
      lE "e" (Idx 1) $
        lE "v" (vecT :@: Idx 2 :@: Idx 1) $
          lE "phi" (natT >-> Ast) $
            lE "z" (Idx 0 :@: zero) $
              lE "c" (pE "n" natT $ Idx 6 >-> Idx 2 :@: Idx 0 >-> Idx 2 :@: (succF :@: Idx 0)) $
                Idx 0 :@: Idx 5 :@: Idx 4 :@: (Idx 3 :@: Idx 2 :@: Idx 1 :@: Idx 0)

consT =
  nf $
    pE "sigma" Ast $
      pE "n" natT $
        Idx 1
          >-> vecT
          :@: Idx 1
          :@: Idx 0
          >-> vecT
          :@: Idx 1
          :@: (succF :@: Idx 0)

vecNatT = nf $ vecT :@: natT

vec12 =
  cons
    :@: natT -- тип
    :@: one -- индекс
    :@: one -- элемент
    :@: ( cons
            :@: natT -- тип
            :@: zero -- индекс
            :@: two -- элемент
            :@: (nil :@: natT)
        )
