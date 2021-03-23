module Lab9

import Lecture9

implementation Semigroup Bool where
  True <+> True = True
  _    <+> _    = False


implementation Monoid Bool where
  neutral = True


reduce : Monoid a => List a -> a
reduce [] = neutral
reduce (x :: xs) = x <+> reduce xs


disjointUnion : Set a -> Set b -> Set (Either a b)
