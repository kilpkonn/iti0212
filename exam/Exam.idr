module Exam

%default total

max3 : Integer -> Integer -> Integer -> Integer
max3 x y z = if x > y then if z > x then z else x 
                      else if z > y then z else y 


tripleMax : (Integer, Integer, Integer) -> Integer
tripleMax (x, (y, z)) = max3 x y z


curry3 : ((a,b,c) -> d) -> (a -> b -> c -> d)
curry3 f x y z = f (x, (y, z))


uncurry3 : (a -> b -> c -> d) -> ((a,b,c) -> d)
uncurry3 f (x, (y, z)) = f x y z


maxList : List Integer -> Integer
maxList xs = foldr (\y, x => if y > x then y else x) 0 xs


printNLines : List String -> IO ()
printNLines [] = pure ()
printNLines (x :: xs) = putStrLn x >>= (\y => printNLines xs)



readNLines : Nat -> IO (List String)
readNLines 0 = pure [] --getLine >>= (\line => pure [line]) 
readNLines (S k) = do
  line <- getLine
  rest <- readNLines k
  pure $ line :: rest 


echoNLines : Nat -> IO ()
echoNLines k = readNLines k >>= (\lines => printNLines lines)


data Fraction : Type where
  MkFraction : (upper: Integer) -> (bottom : Integer) -> Fraction


implementation Eq Fraction where
  (MkFraction upper bottom) == (MkFraction x y) = upper * y == bottom * x
  (MkFraction upper bottom) /= (MkFraction x y) = upper * y /= bottom * x


implementation Num Fraction where
 (MkFraction upper bottom) + (MkFraction x y) = 
   MkFraction (upper * y + x * bottom) (bottom * y)
 (MkFraction upper bottom) * (MkFraction x y) = 
   MkFraction (upper * x) (bottom * y)
 fromInteger n = MkFraction n 1


And  :  (a : Type) -> (b : Type) -> Type
And  =  Pair


Or  :  (a : Type) -> (b : Type) -> Type
Or  =  Either


and_stronger_than_or : a `And` b -> a `Or` b
and_stronger_than_or (x, y) = Left x


and_or : Not (a `Or` b) -> Not (a `And` b) 
and_or f (x, y) = f (Left x)


