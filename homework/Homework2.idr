{-                                                                              
    Tavo Annus                                                                    
    186060IAIB                                                                    
    Idris 2, version 0.3.0-3bbf52025                                              
-}                                                                              
module Homework2

import Lecture7

-- Problem 1
joinIO : IO (IO a) -> IO a
joinIO x = x >>= (\r => r)


mapIO : (a -> b) -> IO a -> IO b
mapIO f x = x >>= (pure . f)


(>=>) : (a -> IO b) -> (b -> IO c) -> a -> IO c
(>=>) f g x = f x >>= g


-- Problem 2
eitherIO : Either (IO a) (IO b) -> IO (Either a b)
eitherIO (Left  x) = x >>= (pure . Left)
eitherIO (Right x) = x >>= (pure . Right)


bothIO : Pair (IO a) (IO b) -> IO (Pair a b)
bothIO (x, y) = do
  xRes <- x
  yRes <- y
  pure (xRes, yRes)


-- Problem 3
implementation Num CoNat where
  (+) Zero     b = b
  (+) (Succ a) b = a + (Succ b)
  (*) (Succ a) (Succ b) = (a + b) + (Succ (a * b)) 
  (*) _        _ = Zero
  fromInteger i = case (the Nat) (fromInteger i) of
                       Z     => Zero
                       (S n) => Succ (fromInteger (i - 1))


implementation Eq CoNat where
  (==) Zero     Zero     = True
  (==) (Succ m) (Succ n) = m == n
  (==) _        _        = False


implementation Ord CoNat where
  compare Zero     Zero     = EQ
  compare Zero     (Succ n) = LT
  compare (Succ n) Zero     = GT
  compare (Succ n) (Succ m) = compare n m


