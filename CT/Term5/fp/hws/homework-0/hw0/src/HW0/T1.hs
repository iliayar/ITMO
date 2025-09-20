{-# LANGUAGE TypeOperators #-}

module HW0.T1 where

data a <-> b = Iso (a -> b) (b -> a)

flipIso :: (a <-> b) -> (b <-> a)
flipIso (Iso f g) = Iso g f

runIso :: (a <-> b) -> (a -> b)
runIso (Iso f _) = f

distrib :: Either a (b, c) -> (Either a b, Either a c)
distrib (Left a) = (Left a, Left a)
distrib (Right (b, c)) = (Right b, Right c)

assocPair :: (a, (b, c)) <-> ((a, b), c)
assocPair = Iso f g
  where
    f :: (a, (b, c)) -> ((a, b), c)
    f (a, (b, c)) = ((a, b), c)

    g :: ((a, b), c) -> (a, (b, c))
    g ((a, b), c) = (a, (b, c))

assocEither :: Either a (Either b c) <-> Either (Either a b) c
assocEither = Iso f g
  where
    f :: Either a (Either b c) -> Either (Either a b) c
    f (Left a) = Left $ Left a
    f (Right (Left b)) = Left $ Right b
    f (Right (Right c)) = Right c

    g :: Either (Either a b) c -> Either a (Either b c)
    g (Left (Left a)) = Left a
    g (Left (Right b)) = Right $ Left b
    g (Right c) = Right $ Right c
