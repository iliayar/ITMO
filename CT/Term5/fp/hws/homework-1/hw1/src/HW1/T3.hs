module HW1.T3
    ( Tree (..)
    , tsize
    , tdepth
    , tmember
    , tinsert
    , tFromList
    ) where

data Tree a = Leaf | Branch !(Int, Int) (Tree a) a (Tree a)

mkBranchRaw :: Tree a -> a -> Tree a -> Tree a
mkBranchRaw left n right =
  Branch
    (tsize left + tsize right + 1, (theight left `max` theight right) + 1)
    left
    n
    right

mkBranch :: Tree a -> a -> Tree a -> Tree a
mkBranch leftTree n rightTree = balance $ mkBranchRaw leftTree n rightTree
  where
    diff :: Tree a -> Int
    diff (Branch _ left _ right) = theight left - theight right
    diff Leaf                    = 0

    balance :: Tree a -> Tree a
    balance t@(Branch _ left _ right) =
      case diff t of
        -2 ->
          case diff right of
            -1 -> rotLeft t
            0  -> rotLeft t
            1  -> bigRotLeft t
            _  -> error "unreachable"
        -1 -> t
        0 -> t
        1 -> t
        2 ->
          case diff left of
            -1 -> bigRotRight t
            0  -> rotRight t
            1  -> rotRight t
            _  -> error "unreachable"
        _ -> error "unreachable"
    balance Leaf = Leaf

    rotLeft, rotRight, bigRotLeft, bigRotRight :: Tree a -> Tree a

    rotRight (Branch _ (Branch _ leftLeft b leftRight) a right) =
      mkBranchRaw leftLeft b (mkBranchRaw leftRight a right)
    rotRight _ = error "unreachable"

    rotLeft (Branch _ left a (Branch _ rightLeft b rightRight)) =
      mkBranchRaw (mkBranchRaw left a rightLeft) b rightRight
    rotLeft _ = error "unreachable"

    bigRotLeft (Branch _ left a right) =
      rotLeft $ mkBranchRaw left a (rotRight right)
    bigRotLeft _ = error "unreachable"

    bigRotRight (Branch _ left a right) =
      rotRight $ mkBranchRaw (rotLeft left) a right
    bigRotRight _ = error "unreachable"

tsize :: Tree a -> Int
tsize Leaf                     = 0
tsize (Branch (size, _) _ _ _) = size

theight :: Tree a -> Int
theight Leaf                       = 0
theight (Branch (_, height) _ _ _) = height

tdepth :: Tree a -> Int
tdepth = theight

tmember :: Ord a => a -> Tree a -> Bool
tmember _ Leaf = False
tmember e (Branch _ left n right) =
  case compare e n of
    LT -> tmember e left
    EQ -> True
    GT -> tmember e right

tinsert :: Ord a => a -> Tree a -> Tree a
tinsert e Leaf = mkBranch Leaf e Leaf
tinsert e b@(Branch _ left n right) =
  case compare e n of
    LT -> mkBranch (tinsert e left) n right
    EQ -> b
    GT -> mkBranch left n (tinsert e right)

tFromList :: Ord a => [a] -> Tree a
tFromList = foldl (flip tinsert) Leaf
