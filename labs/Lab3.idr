import Data.Vect
import Data.Nat

swapPair : (a, b) -> (b, a)
swapPair (a, b) = (b, a)

swapEither : (Either a b) -> (Either b a)
swapEither (Left a)  = Right a
swapEither (Right b) = Left b

there : Nat -> List Unit
there 0 = []
there (S k) = () :: (there k)

back : List Unit -> Nat
back [] = 0
back (x :: xs) = S (back xs)

project : Fin n -> Nat
project FZ = Z
project (FS x) = S (project x)

listify : Vect n a -> List a
listify [] = []
listify (x :: xs) = x :: (listify xs)

reverseList : List a -> List a
reverseList xs = revAcc [] xs where
  revAcc : List a -> List a -> List a
  revAcc acc []        = acc
  revAcc acc (x :: xs) = revAcc (x :: acc) xs

reverseVect : Vect n a -> Vect n a
reverseVect xs = revAcc [] xs where
  revAcc : Vect k a -> Vect l a -> Vect (k + l) a
  revAcc {k}         acc []        = rewrite plusZeroRightNeutral k in acc
  revAcc {k} {l=S l} acc (x :: xs) = rewrite sym $ plusSuccRightSucc k l in revAcc (x :: acc) xs

-- TODO: What is this "rewrite sym $ rule x y in expr"

data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

size : Tree a -> Nat
size Leaf         = 0
size (Node l n r) = (size l) + 1 + (size r)

depth : Tree a -> Nat
depth Leaf         = 0
depth (Node l n r) = 1 + (max (depth l) (depth r))

flatten : Tree a -> List a
flatten Leaf = []
flatten (Node l n r) = (flatten l) ++ (n :: (flatten r))

