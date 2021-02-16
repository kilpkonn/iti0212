{-
  Tavo Annus
  186060IAIB
  Idris 2, version 0.3.0-3bbf52025
-}
import Data.Strings
import Data.Vect

-- Problem 1
ack : Nat -> Nat -> Nat
ack 0     n     = n + 1
ack (S m) 0     = ack m 1
ack (S m) (S n) = ack m (ack (S m) n)


-- Problem 2
diag : a -> Pair a a
diag x = (x, x)

anyway : Either a a -> a
anyway (Left x)  = x
anyway (Right x) = x

assocr : Pair (Pair a b) c -> Pair a (Pair b c)
assocr ((x, y), z) = (x, (y, z))

distl : Pair a (Either b c) -> Either (Pair a b) (Pair a c)
distl (x, (Left y))  = Left (x, y)
distl (x, (Right z)) = Right (x, z)


-- Problem 3
consolidate : List (Maybe a) -> Maybe (List a)
consolidate []               = Just []
consolidate (x :: xs) = consAdd x (consolidate xs) where
  consAdd : Maybe a -> Maybe (List a) -> Maybe (List a)
  consAdd Nothing  x         = Nothing
  consAdd x        Nothing   = Nothing
  consAdd (Just x) (Just xs) = Just (x :: xs)


-- Problem 4
transform : (f : a -> a) -> (index : Nat) -> List a -> List a
transform f index []        = []
transform f 0     (x :: xs) = (f x) :: xs
transform f (S k) (x :: xs) = x :: (transform f k xs)


-- Problem 5
titlecase : String -> String
titlecase str = unwords (map (\word => pack (transform (\c => toUpper c) 0 (unpack word))) (words str))
-- This is VERY slow


-- Problem 6
Matrix : Nat -> Nat -> Type -> Type
Matrix m n t = Vect m (Vect n t)

add : Matrix m n Integer -> Matrix m n Integer -> Matrix m n Integer
add [] [] = []
add (x :: xs) (y :: ys) = (addRow x y) :: (add xs ys) where
  addRow : (as : Vect n Integer) -> (bs : Vect n Integer) -> Vect n Integer
  addRow as bs = zipWith (\a, b => a + b) as bs                              -- This can be written inline in add, but keeping for readability

-- add (the (Matrix 3 2 Integer)[[1, 2], [2, 3], [4, 5]]) (the (Matrix 3 2 Integer) [[1, 1], [1, 2], [1, 3]])
 
    


