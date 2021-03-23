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
disjointUnion xs ys = do
  x <- xs
  y <- ys
  pure (Left x) `set_union` pure (Right y)


myJoin : Monad t => t (t a) -> t a
myJoin xs = xs >>= (\x => x)


glueTrees : Tree a -> Tree a -> Tree a -> Tree a
glueTrees (Leaf label) y z = Node label y z
glueTrees (Node label child1 child2) y z = 
  Node label (glueTrees child1 y z) (glueTrees child2 y z)


implementation Functor Tree where
  map f (Leaf label) = Leaf $ f label
  map f (Node label child1 child2) = 
    Node (f label) (map f child1) (map f child2)


implementation Applicative Tree where
  pure x = Leaf x
  (Leaf f) <*> t = map f t
  (Node f child1 child2) <*> t = glueTrees (map f t) (child1 <*> t) (child2 <*> t)


implementation Monad Tree where
  (Leaf label) >>= f = f label
  (Node label child1 child2) >>= f = glueTrees (f label) (child1 >>= f) (child2 >>= f)


sapling : Unit -> Tree Unit
sapling () = Node () (Leaf ()) (Leaf ())

depth : Tree a -> Nat
depth (Leaf label) = 1
depth (Node label child1 child2) = 1 + max (depth child1) (depth child2)


makeTree : (n : Nat) -> Tree ()
makeTree Z = Leaf ()
makeTree (S n) = do
  glueTrees (makeTree n) (makeTree n) (makeTree n)


