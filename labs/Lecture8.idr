import Data.List
import Data.Vect


-- polymorphism - no assumptions about the structure of the types involved

my_id : a -> a
my_id x = x

zipvect : Vect n a -> Vect n b -> Vect n (Pair a b)
zipvect [] [] = []
zipvect (x :: xs) (y :: ys) = (x, y) :: (zip xs ys)

plus : Num a => a -> a -> a
plus x y = x + y


-- interfaces
-- a signature that specifies some operations (like an abstract class in Java or C++)
--
-- the idea is that different types will have custom implementations of the operations
-- this concept is known as ad-hoc polymorphism

-----------------------------------------------------
--               The Show interface                --
-----------------------------------------------------


{--

interface Show a where
    show : a -> String

--}

{-
data Shape = IsoTriangle Double Double
            | Rectangle Double Double
            | Circle Double
-}

data Shape : Type where
  IsoTriangle : Double -> Double -> Shape
  Rectangle : Double -> Double -> Shape
  Circle : Double -> Shape

implementation Show Shape where
  show (IsoTriangle x y) = "Triangle with base " ++ show x ++ " and height " ++ show y
  show (Rectangle x y) = "Rectangle with width" ++ show x ++ " and height " ++ show y
  show (Circle x) = "Circle with radius " ++ show x

-- using Alternative implementations

implementation [KleenePurist] Show Nat where
  show Z = "Z"
  show (S k) = "S(" ++ show k ++ ")"

  -- show @{KleenePurist} 3


---------------------------------------------------------
--        Using an interface as a constraint           --
---------------------------------------------------------

compliment : Show a => a -> String
compliment x = "Oh what a nice " ++ show x ++ " you are."

implementation [ListShow] Show a => Show (List a) where
  show [] = ""
  show (x :: []) =  show x
  show (x :: (y :: xs)) =  show x ++ ", " ++ show @{ListShow} (y :: xs)

  -- show @{ListShow} [1,2,3]

-----------------------------------------------------
--               The Eq interface                  --
-----------------------------------------------------

{-
interface Eq a where
    (==) : a -> a -> Bool
    (/=) : a -> a -> Bool

    x /= y = not (x == y)
    x == y = not (x /= y)
-}

-- Defining equality

implementation Eq Shape where
  (==) (IsoTriangle x y) (IsoTriangle z w) = (x == z) && (y == w)
  (==) (Rectangle x y) (Rectangle z w) = (x == z) && (y == w)
  (==) (Circle x) (Circle y) = (x == y)
  (==) _ _ = False

-- Using Eq interface to count occurences in a list

multiplicity : Eq a => a -> List a -> Nat
multiplicity target = length . filter (target ==)


-- redifine
-- implementation [NatEq] Eq Nat where
--  m == n = ?nat_eq

implementation [NatEq] Eq Nat where
  Z == Z = True
  (S k) == (S j) = (==) @{NatEq} k j
  _ == _ = False

-- (==) @{NatEq} 3 3


------------------------------------------------------
--               The Ord interface                  --
------------------------------------------------------


{-
  data Ordering = LT | EQ | GT

  interface Eq a => Ord a where
    compare : a -> a -> Ordering

    (<) : a -> a -> Bool
    (>) : a -> a -> Bool
    (<=) : a -> a -> Bool
    (>=) : a -> a -> Bool
    max : a -> a -> a
    min : a -> a -> a
-}


-- sort : Ord a => List a -> List a

check_sorted : Ord a => List a -> Bool
check_sorted [] = True
check_sorted (x :: []) = True
check_sorted (x :: (y :: xs)) = (x <= y) && check_sorted (y :: xs)


-------------------------------------------------------
--               The Cast interface                  --
-------------------------------------------------------

{-
Prelude.Cast : Type -> Type -> Type
	 Interface for transforming an instance of a data type to another type.
Parameters: from, to

Methods:
cast : (orig : from) -> to
	 Perform a (potentially lossy!) cast operation.
	 @ orig The original type

-}


------------------------------------------------------
--               The Num interface                  --
------------------------------------------------------

{-
Prelude.Num : Type -> Type
	 The Num interface defines basic numerical arithmetic.
Parameters: ty

Methods:
+ : ty -> ty -> ty
* : ty -> ty -> ty
fromInteger : Integer -> ty
	 Conversion from Integer.
-}

-- complex numbers as pairs of reals, i.e. (a,b) := a + ib
-- (a + ib) + (c + id) := a+c + i(b+d)
-- (a + ib) * (c + id) := a*c - b*d + i(b*c + a*d)

data GaussianInteger : Type where
   Gauss : Integer -> Integer -> GaussianInteger

implementation Cast Integer GaussianInteger where
  cast x = Gauss x 0

implementation Show GaussianInteger where
  show (Gauss x y) = show x ++ complex_part y where
    complex_part : Integer -> String
    complex_part x = case x of
                      0 => ""
                      otherwise => (if x > 0 then " + " else " - ")
                                      ++ (if (x /= 1) && (x /= -1) then show (abs x) else "")
                                        ++ "i"


-- (a + ib) + (c + id) := a+c + i(b+d)
-- (a + ib) * (c + id) := a*c - b*d + i(b*c + a*d)


implementation Num GaussianInteger where
  (+) (Gauss a b) (Gauss c d) = Gauss (a + c) (b + d)
  (*) (Gauss a b) (Gauss c d) = Gauss (a * c - b * d) (b * c + a * d)
  fromInteger n = cast n



--------------------------------------------------------
--            Defining an interface                   --
--------------------------------------------------------

interface Mag a where
  magnitude : a -> Double

-- sumofsquares : (Num a) => Vect k a -> a
-- sumofsquares [] = 0
-- sumofsquares (x :: xs) = x * x + (sumofsquares xs)

-- sumofsquares : (Num a) => Vect k a -> a
-- sumofsquares = foldr (\x,y => x*x + y) 0

-- [a, b, c, d] |-> sqrt(a^2 + b^2 + c^2 + d^2)

--implementation  (Num a, Cast a Double) => Mag (Vect k a) where
--  magnitude  = sqrt . cast . sumofsquares where
--    sumofsquares : (Num a) => Vect k a -> a
--    sumofsquares = foldr (\x,y => (x * x) + y) 0


implementation Cast GaussianInteger (Vect 2 Integer) where
  cast (Gauss x y) = [x,y]

implementation Mag GaussianInteger where
  magnitude (Gauss a b) = sqrt $ cast (a*a + b*b)
