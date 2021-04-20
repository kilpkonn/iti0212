module Lab13

import Lecture11
import Lecture13

%default total


contrapositive : (a -> b) -> Not b -> Not a
contrapositive f g x = g (f x)


dni : a -> Not $ Not a
dni x f = f x


tnr : Not $ Not $ Not a -> Not a
tnr f x = f (\k => k x)


%hide Prelude.Stream.(::)
heads_differ : Not (x = y) -> Not (x :: xs = y :: ys)
heads_differ f Refl = f Refl 


tails_differ : Not (xs = ys) -> Not (x :: xs = y :: ys)
tails_differ f Refl = f Refl


double_child_even : Even (S (S n)) -> Even n
double_child_even (SS_even x) = x


odd_or_even : (n : Nat) -> Odd n `Or` Even n
odd_or_even 0 = Right Z_even
odd_or_even (S 0) = Left one_odd
odd_or_even (S (S n)) with (odd_or_even n)
  odd_or_even (S (S n)) | (Left n_odd) = Left $ n_odd . double_child_even
  odd_or_even (S (S n)) | (Right n_even) = Right $ SS_even n_even
