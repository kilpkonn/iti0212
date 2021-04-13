{-                                                                              
    Tavo Annus                                                                    
    186060IAIB                                                                    
    Idris 2, version 0.3.0-3bbf52025                                              
-}                                                                              
module Homework3

import Data.Vect
import Data.List.Elem


%default total


-- Problem 1
implementation Semigroup (a -> a) where
  (<+>) f g = g . f


implementation Monoid (a -> a) where
  neutral = id


-- Problem 2
applicify : {t : Type -> Type} -> Applicative t => (op : a -> a -> a) -> t a -> t a -> t a
applicify op x y = pure op <*> x <*> y


infixl 7 +?
(+?) : Num a => Maybe a -> Maybe a -> Maybe a
(+?) = applicify (+)

infixl 7 +*
(+*) : Num a => {n : Nat} -> Vect n a -> Vect n a -> Vect n a
(+*) = applicify (+)


-- Problem 3
mapPair : (f : a -> a') -> (g : b -> b') -> Pair a b -> Pair a' b'
mapPair f g (x, y) = (f x, g y)


mapDPair : (f : a -> a') -> (g : {x : a} -> b x -> b' (f x)) -> DPair a b -> DPair a' b'
mapDPair f g (MkDPair fst snd) = (f fst ** g snd)


-- Problem 4
ary_op : (arity : Nat) -> Type -> Type
ary_op 0     t = t
ary_op (S n) t = t -> ary_op n t


-- Problem 5
in_left : Elem z xs -> (ys : List a) -> Elem z (xs ++ ys)  
in_left Here ys = Here
in_left (There x) ys = There $ in_left x ys


-- Problem 6
in_right : Elem z ys -> (xs : List a) -> Elem z (xs ++ ys)
in_right x [] = x
in_right x (y :: xs) = There (in_right x xs)




