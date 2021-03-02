module Lab6

import Data.Fin
import Data.Vect

data Shape : Type where
  Circle      : (radius : Double) -> Shape
  Rectangle   : (height, width : Double) -> Shape
  IsoTriangle : (base, height : Double) -> Shape
  Star        : (n, length, height: Double) -> Shape

area : Shape -> Double 
area (Circle radius) = pi * radius * radius
area (Rectangle height width) = height * width
area (IsoTriangle base height) = base * height / 2
area (Star n length height) = n * (area (IsoTriangle length height))

indexList : (index : Nat) -> List a -> Maybe a
indexList index []        = Nothing
indexList 0     (x :: xs) = Just x
indexList (S k) (_ :: xs) = indexList k xs

indexVect : (index : Fin n) -> Vect n a -> a
indexVect FZ     (x :: xs) = x
indexVect (FS y) (_ :: xs) = indexVect y xs

data Tree : Type -> Type where
  Leaf : Tree a
  Node : (left : Tree a) -> (this : a) -> (right : Tree a) -> Tree a

zipTree : (a -> b -> c) -> Tree a -> Tree b -> Tree c
zipTree f Leaf                      _                         = Leaf
zipTree f _                         Leaf                      = Leaf
zipTree f (Node leftA thisA rightA) (Node leftB thisB rightB) =
  Node (zipTree f leftA leftB) (f thisA thisB) (zipTree f rightA rightB)

foldMaybe : (f : a -> b) -> (n : b) -> Maybe a -> b
foldMaybe f n Nothing  = n
foldMaybe f n (Just x) = f x

mapMaybe : (a -> b) -> Maybe a -> Maybe b
mapMaybe f x = foldMaybe (\y => Just (f y)) Nothing x

tryIOs : List (IO (Either error Unit)) -> IO (Maybe error)
tryIOs []        = pure Nothing
tryIOs (x :: xs) = x >>= 
  (\res => case res of
                Left err => pure $ Just err
                Right () => tryIOs xs
  )

batchIOs : List (IO (Either error Unit)) -> IO (List error)
batchIOs []        = pure []
batchIOs (x :: xs) = do
  res <- x
  errors <- batchIOs xs
  case res of
       Left err => pure (err :: errors)
       Right () => batchIOs xs


