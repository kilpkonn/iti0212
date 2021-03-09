import Lecture7

length : CoList a -> CoNat
length []        = Zero
length (x :: xs) = Succ $ length xs

drop : Nat -> CoList a -> CoList a
drop 0     xs        = xs
drop (S k) []        = []
drop (S k) (x :: xs) = drop k xs

filter : (a -> Bool) -> CoList a -> CoList a
filter f []        = []
filter f (x :: xs) = case f x of
                          True  => x :: (filter f xs)
                          False => filter f xs

inf_filter : CoList Nat
inf_filter = filter (\_ => False) infGen where
  infGen : CoList Nat
  infGen = Z :: infGen

zipStreamList : (a -> b -> c) -> Stream a -> List b -> List c
zipStreamList f (x :: y) []        = []
zipStreamList f (x :: y) (z :: zs) = f x z :: (zipStreamList f y zs)

enumerate : List a -> List (Pair Nat a)
enumerate xs = zipStreamList (\i, el => (i, el)) natStream xs

minus : CoNat -> CoNat -> CoNat
minus Zero     y        = Zero
minus (Succ n) Zero     = n
minus (Succ n) (Succ x) = minus n x

times : (a : CoNat) -> (b : CoNat) -> CoNat
times Zero     _         = Zero
times _        Zero      = Zero
times (Succ a) (Succ b)  = (a `plus` b) `plus` (Succ (a `times` b))
