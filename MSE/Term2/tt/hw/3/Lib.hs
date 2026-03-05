import Control.Monad (guard)

type Symb = String

infixr 3 :->

data Type
  = TVar Symb -- типовый атом
  | Type :-> Type -- стрелочный тип
  deriving (Read, Show, Eq, Ord)

type Ctx = [Type] -- контекст

data TNF
  = Meta -- метапеременная (пока еще бесструктурная часть схемы)
      Type -- типизирована
  | TNF -- структурированная часть схемы
      Ctx -- абстрактор
      Int -- головная переменная как индекс Де Брауна
      [TNF] -- бёмовы хвостики
  deriving (Read, Show, Eq, Ord)

uncurry2List :: Type -> (Symb, [Type])
uncurry2List (TVar ret) = (ret, [])
uncurry2List (l :-> r) =
  let (ret, args) = uncurry2List r
   in (ret, l : args)

uncurry2RevList :: Type -> (Symb, [Type])
uncurry2RevList = uncurry2RevList' []
  where
    uncurry2RevList' :: [Type] -> Type -> (Symb, [Type])
    uncurry2RevList' args (TVar ret) = (ret, args)
    uncurry2RevList' args (l :-> r) = uncurry2RevList' (l : args) r

unMeta :: Ctx -> TNF -> [TNF]
unMeta zetas (Meta ty) = do
  let (ret, args) = uncurry2RevList ty
      zetas' = args ++ zetas
  (fArg, idx) <- zip zetas' [0 ..]
  let (fRet, mArgs) = uncurry2List fArg
  guard $ fRet == ret
  return $ TNF args idx $ map Meta mArgs
unMeta zetas (TNF ctx idx tnfs) = do
  let zetas' = ctx ++ zetas
  tnfs' <- mapM (unMeta zetas') tnfs
  return $ TNF ctx idx tnfs'

isTerm :: TNF -> Bool
isTerm (Meta _) = False
isTerm (TNF _ _ args) = all isTerm args

allTNFGens :: Type -> [[TNF]]
allTNFGens t = allTNFGens' [Meta t]
  where
    allTNFGens' :: [TNF] -> [[TNF]]
    allTNFGens' [] = []
    allTNFGens' prev = 
        if all isTerm prev then [prev]
        else prev : allTNFGens' (concat $ fmap (unMeta []) $ filter (not . isTerm) prev)

inhabGens :: Type -> [[TNF]]
inhabGens t = fmap (filter isTerm) $ allTNFGens t

inhabs :: Type -> [TNF]
inhabs = concat . inhabGens

tArr = TVar "a" :-> TVar "a"

tNat = tArr :-> tArr

tBool = TVar "a" :-> TVar "a" :-> TVar "a"

tK = TVar "a" :-> TVar "b" :-> TVar "a"

tKast = TVar "a" :-> TVar "b" :-> TVar "b"

tBiNat = (TVar "a" :-> TVar "a") :-> (TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"

tBiBiNat = (TVar "a" :-> TVar "b") :-> (TVar "b" :-> TVar "a") :-> TVar "a" :-> TVar "a"

tBinTree = (TVar "a" :-> TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"

hw3last1 = ((TVar "a" :-> TVar "b") :-> TVar "a") :-> (TVar "a" :-> TVar "a" :-> TVar "b") :-> TVar "a"

hw3last2 = ((TVar "a" :-> TVar "b") :-> TVar "a") :-> (TVar "a" :-> TVar "a" :-> TVar "b") :-> TVar "b"

t3 = ((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a"

contFmapT =
  (TVar "a" :-> TVar "b")
    :-> ((TVar "a" :-> TVar "c") :-> TVar "d")
    :-> (TVar "b" :-> TVar "c")
    :-> TVar "d"

selFmapT =
  (TVar "a" :-> TVar "b")
    :-> ((TVar "a" :-> TVar "c") :-> TVar "a")
    :-> (TVar "b" :-> TVar "c")
    :-> TVar "b"

monsterT = (((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a") :-> TVar "a" :-> TVar "a"

fixT = (TVar "a" :-> TVar "a") :-> TVar "a"

peirceT = ((TVar "p" :-> TVar "q") :-> TVar "p") :-> TVar "p"
