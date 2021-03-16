import Data.List

import Lecture8    


implementation Neg GaussianInteger where
  negate (Gauss a b) = Gauss (negate a) (negate b)


implementation Eq GaussianInteger where
  (==) (Gauss a b) (Gauss c d) = (a == c) && (b == d)


implementation [lex] Ord GaussianInteger where
  compare (Gauss a b) (Gauss c d) = compare a c


implementation [mag] Ord GaussianInteger where
  compare a b = compare (magnitude a) (magnitude b)


implementation [setwise] Eq a => Eq (List a) where
  (==) xs ys = (all id (map (\e => elem e ys) xs)) &&
               (all id (map (\e => elem e xs) ys))


implementation [multisetwise] Eq a => Eq (List a) where
  (==) []        [] = True
  (==) (x :: xs) ys = case elem x ys of
                         False => False
                         True  => (==) @{multisetwise} (delete x xs) (delete x ys)  
  (==) _         _ = False
  
