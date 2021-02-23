
beep : (Pair a b -> c) -> (a -> b -> c)
beep f x y= f (x, y)

boop : (a -> b -> c) -> (Pair a b -> c)
boop f (x, y) = f x y

conjunction : Bool -> Bool -> Bool
conjunction x False = False 
conjunction False y = False
conjunction x y     = True

disjunction : Bool -> Bool -> Bool
disjunction x True = True
disjunction True y = True
disjunction x y    = False


foldList : (a -> b -> b) -> b -> List a -> b
foldList f y []        = y
foldList f y (x :: xs) = f x (foldList f y xs)

conj : List Bool -> Bool
conj xs = foldList conjunction True xs

disj : List Bool -> Bool
disj xs = foldList disjunction False xs

filterList : (a -> Bool) -> List a -> List a
filterList f []        = []
filterList f (x :: xs) = case f x of
                              True  => x :: (filterList f xs)
                              False => filterList f xs


data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a

foldTree : (a -> b -> b) -> b -> Tree a -> b
foldTree f na Leaf              = na
foldTree f na (Node child node) = f node (foldTree f na child)

mapTree : (a -> b) -> Tree a -> Tree b 
mapTree f tree = foldTree (\x, newTree => Node newTree (f x)) Leaf tree

sumTree : Tree Nat -> Nat
sumTree tree = foldTree (\x, sum => x + sum) 0 tree
