import qualified Data.Map as Map
import qualified Data.List as List
import Control.Monad (guard, mzero)

type Symb = String

-- Типы-пересечения (1 способ)
infixr 4 :->
infixr 5 :/\
data Type = TVar Symb         -- типовой атом 
          | Type :-> Type     -- стрелочный тип
          | Type :/\ Type     -- тип пересечение
          | Univ              -- универсальный тип
    deriving (Read,Show)

-- Типы-пересечения (2 способ)
newtype IType = I [SType]      -- тип-пересечение 
    deriving (Read,Show)

-- Простые типы
infixr 4 :-->
data SType = STVar Symb        -- типовой атом 
           | IType :--> IType  -- стрелочный тип
    deriving (Read,Show)

instance Eq Type where
  l == r = toI l == toI r

instance Eq IType where
  (I l) == (I r) = all (flip elem r) l && all (flip elem l) r

instance Eq SType where
  (STVar sl) == (STVar sr) = sl == sr
  (ll :--> lr) == (rl :--> rr) = ll == rl && lr == rr
  _ == _ = False

toI :: Type -> IType
toI (TVar s) = I [STVar s]
toI (l :-> r) = I [toI l :--> toI r]
toI (l :/\ r) =
  let (I l') = toI l
      (I r') = toI r
   in I $ l' ++ r'
toI Univ = I []

fromI :: IType -> Type
fromI (I []) = Univ
fromI (I vs) = foldr1 (:/\) $ map fromI' vs
  where
    fromI' :: SType -> Type
    fromI' (STVar s) = TVar s
    fromI' (l :--> r) = fromI l :-> fromI r

alphaEqTy :: Type -> Type -> Bool
alphaEqTy l r = alphaEqITy (toI l) (toI r)

alphaEqITy :: IType -> IType -> Bool
alphaEqITy l r = not $ List.null $ eqI 0 Map.empty Map.empty l r

alphaEqSTy :: SType -> SType -> Bool
alphaEqSTy l r = not $ List.null $ eqS 0 Map.empty Map.empty l r

type Subst = Map.Map Symb Int

eqI :: Int -> Subst -> Subst -> IType -> IType -> [(Int, Subst, Subst)]
eqI vc sl sr (I l) (I r) = trySubsts vc sl sr (List.nub l) (List.nub r)

trySubsts :: Int -> Subst -> Subst -> [SType] -> [SType] -> [(Int, Subst, Subst)]
trySubsts vs sl sr [] [] = return (vs, sl, sr)
trySubsts _ _ _ [] _ = mzero
trySubsts _ _ _ _ [] = mzero
trySubsts vc sl sr tls trs = do
  pl <- List.permutations tls
  pr <- List.permutations trs
  tryPerm vc sl sr pl pr
  where
    tryPerm :: Int -> Subst -> Subst -> [SType] -> [SType] -> [(Int, Subst, Subst)]
    tryPerm vc sl sr [] [] = return (vc, sl, sr)
    tryPerm vc sl sr (tl : tls) (tr : trs) = do
      (vc', sl', sr') <- eqS vc sl sr tl tr
      tryPerm vc' sl' sr' tls trs
    tryPerm _ _ _ _ _ = mzero

eqS :: Int -> Subst -> Subst -> SType -> SType -> [(Int, Subst, Subst)]
eqS vc sl sr (STVar l) (STVar r) =
  case (Map.lookup l sl, Map.lookup r sr) of
    (Just l', Just r') -> do
        guard $ l' == r'
        return (vc, sl, sr)
    (Just l', Nothing) -> mzero
    (Nothing, Just r') -> mzero
    _ -> return (vc + 1, Map.insert l vc sl, Map.insert r vc sr)
eqS vc sl sr (ll :--> lr) (rl :--> rr) = do
  (vc', sl', sr') <- eqI vc sl sr ll rl
  eqI vc' sl' sr' lr rr
eqS _ _ _ _ _ = mzero

type Ctx = [[Type]] -- контекст

curryFrom :: Ctx -> Type -> Type
curryFrom [] ty = ty
curryFrom (vty : vtys) ty = 
    let aty = fromI $ I $ concat $ map (\(I tys) -> tys) $ map toI vty
    in curryFrom vtys $ aty :-> ty

data TermNF = Trm
              Int      -- абстрактор (число биндеров)
              Int      -- головная переменная (индекс де Брауна)
              [TermNF] -- аргументы (Бёмовы хвостики)
    deriving (Read,Show,Eq,Ord)

icomb, zero, one, two, three :: TermNF
icomb = Trm 1 0 []                               -- \x -> x
zero  = Trm 2 0 []                               -- \s z -> z
one   = Trm 2 1 [Trm 0 0 []]                     -- \s z -> s z
two   = Trm 2 1 [Trm 0 1 [Trm 0 0 []]]           -- \s z -> s (s z)
three = Trm 2 1 [Trm 0 1 [Trm 0 1 [Trm 0 0 []]]] -- \s z -> s( s (s z))

kcomb, kastcomb, ccomb, bcomb, scomb :: TermNF
kcomb = Trm 2 1 []                                 -- \x y -> x
kastcomb = Trm 2 0 []                              -- \x y -> y
ccomb = Trm 3 2 [Trm 0 0 [],Trm 0 1 []]            -- \f y x -> f x y
bcomb = Trm 3 2 [Trm 0 1 [Trm 0 0 []]]             -- \f g x -> f (g x)
scomb = Trm 3 2 [Trm 0 0 [], Trm 0 1 [Trm 0 0 []]] -- \f g x -> f x (g x)

omega, omega', omega'' :: TermNF
omega   = Trm 1 0 [Trm 0 0 []]             -- \x -> x x
omega'  = Trm 1 0 [Trm 0 0 [], Trm 0 0 []] -- \x -> x x x
omega'' = Trm 1 0 [Trm 0 0 [Trm 0 0 []]]   -- \x -> x (x x)

test1,test2,test3,test4,test5,test6 :: TermNF
test1 = Trm 2 0 [Trm 0 1 []]            -- \x y -> y x
test2 = Trm 2 1 [Trm 0 0 [Trm 0 1 []]]  -- \x y -> x (y x)
test3 = Trm 2 1 [Trm 0 0 [],Trm 0 1 []] -- \x y -> x y x
test4 = Trm 1 0 [Trm 1 0 []]            -- \f -> f (\x -> x)           :: ((p -> p) -> t) -> t
test5 = Trm 1 0 [Trm 1 1 [Trm 1 0 []]]  -- \f -> f (\x -> f (\y -> y)) :: ((p -> p) -> p) -> p
test6 = Trm 1 0 [Trm 1 1 [Trm 1 1 []]]  -- \f -> f (\x -> f (\y -> x)) :: ((p -> p) -> p) -> p

sscomb, ssscomb, ucomb, diagP :: TermNF
sscomb = Trm 3 1 [Trm 0 0 [], Trm 0 2 [Trm 0 1 [],Trm 0 0 []]]                       -- \f g x -> g x (f g x)
ssscomb = Trm 3 2 [Trm 0 1 [],Trm 0 0 [], Trm 0 1 [Trm 0 2 [Trm 0 1 []],Trm 0 0 []]] -- \f g x -> f g x (g (f g) x)
ucomb = Trm 4 3 [Trm 0 0 [],Trm 0 2 [Trm 0 0 [],Trm 0 1 [Trm 0 0 []]]]             -- \f g h x -> f x (g x (h x))
diagP = Trm 3 0 [Trm 0 2 [Trm 0 1 []],Trm 0 2 [Trm 0 1 []]]                          -- \g a f -> f (g a) (g a)

infer :: TermNF -> (Ctx, Type)
infer term = let (_, ctx, ty) = infer' 0 [] term in (ctx, ty)
  where
    addAt :: Int -> Type -> [[Type]] -> [[Type]]
    addAt i x xs =
      let xs' = if i >= length xs then xs ++ (replicate (i - length xs + 1) []) else xs
       in take i xs' ++ [x : (xs' !! i)] ++ drop (i + 1) xs'

    infer' :: Int -> Ctx -> TermNF -> (Int, Ctx, Type)
    infer' vc ctx (Trm nabs hv args) =
      let retTy = TVar $ show vc
          (vc', ctx', argTys) =
            foldr
              ( \arg (vc, ctx, tys) ->
                  let (vc', ctx', ty) = infer' vc ctx arg
                   in (vc', ctx', ty : tys)
              )
              (vc + 1, replicate nabs [] ++ ctx, [])
              args
          (abTys, ctx'') = splitAt nabs ctx'
          hty = foldr (:->) retTy argTys
       in if hv >= nabs
            then (vc', addAt (hv - nabs) hty ctx'', curryFrom abTys retTy)
            else (vc', ctx'', curryFrom (addAt hv hty abTys) retTy)

-- для комбинаторов достаточно
infer0 :: TermNF -> Type
infer0 = snd . infer
