#import "common.typ": *

#show: doc => practice(
  subj: [Теория Типов],
  title: [Практика 9],
  date: [8 апреля],
  number: 9,
  author: "Ярошевский Илья",
  doc
)

#task(numbering: (..) => numbering("1", 1))[
  ```hs
  data Rec = forall a. Rec {a :: a, f :: a -> Int}
  
  fromRec :: Rec -> forall r. (forall a. a -> (a -> Int) -> r) -> r
  fromRec (Rec {a, f}) abs = abs a f
  
  toRec :: (forall r. (forall a. a -> (a -> Int) -> r) -> r) -> Rec
  toRec abs = abs $ \a f -> Rec {a = a, f = f}
  
  p1,p2 :: Rec
  p1 = Rec 5 succ
  p2 = Rec True (\_ -> 42)
  
  f1 :: Rec-> Int
  f1 (Rec val fun) = fun val
  ```

  ```
  ghci> :t fromRec p1
  fromRec p1 :: (forall a. a -> (a -> Int) -> r) -> r
  ghci> fromRec p1 (\val fun -> fun val)
  6
  ghci> fromRec p2 (\val fun -> fun val)
  42
  ghci> :t toRec $ fromRec p1
  toRec $ fromRec p1 :: Rec
  ghci> f1 $ toRec $ fromRec p1
  6
  ```
]
