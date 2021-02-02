-- There is only one function Bool -> Unit as there is only one return type. 
-- (Can agrue there is 2 different input tho so depends on definition a little bit)
bool_to_unit : Bool -> Unit
bool_to_unit True  = ()
bool_to_unit False = ()  -- I'd say it's same as first line...

-- There are 2 functions Bool -> Bool (techincallly 4 but only 2 can be defined at once)
bool_to_bool : Bool -> Bool
bool_to_bool True  = False
bool_to_bool False = True

-- Only one output so only one meaningful function, althogh you can write same for every Nat...
nat_to_unit : Nat -> Unit
nat_to_unit k = ()

-- Only one input so only one function
unit_to_nat : Unit -> Nat
unit_to_nat x = Z  -- Instead of 0 you can use any Nat but only one can be defined at time

-- Only one, that is impossible. So is this considered 0 as we can't constuct Void
void_to_void : Void -> Void
-- void_to_void x = impossible

-- Again not possible, as we can't construct Void
nat_to_void : Nat -> Void
-- nat_to_void = impossible

-- Sama same as previous, only that we can't construct argument instead of result
void_to_nat : Void -> Nat
-- void_to_nat = impossible


data Shape : Type where
  Circle : Nat -> Shape
  Rectangle : Nat -> Nat -> Shape
  IsoTriangle : Nat -> Nat -> Shape  -- This might result in illegal triangles
  IsoTriangle2 : Nat -> Nat -> Shape  -- This has side and height, not sure if there is better way to distinct them
  RegPolygon : Nat -> Nat -> Shape

area : Shape -> Double
area (Circle r)         = pi * (cast (r * r))
area (Rectangle a b)    = cast (a * b)
area (IsoTriangle a b)  = (cast a) * ((cast b) * sin(pi / 2.0 - (cast a) / (2 * (cast b)))) / 2.0
area (IsoTriangle2 a h) = (cast (a * h)) / 2.0
area (RegPolygon n a)   = ((pow (cast a) 2) * (cast n)) / (4.0 * tan(pi / (cast n)))

regular : Shape -> Bool
regular (Circle r)         = True  -- Not sure of mathematical definition, but since there are no unequal sides I'd say True
regular (Rectangle a b)    = a == b
regular (IsoTriangle a b)  = a == b
regular (IsoTriangle2 a h) = cast a == sqrt (cast (a * a + h * h))
regular (RegPolygon a b)   = True

monus : Nat -> Nat -> Nat
monus Z _         = Z 
monus (S a) Z     = S a
monus (S a) (S b) = monus a b

even : Nat -> Bool
even Z     = True
even (S n) = not (even n)

odd : Nat -> Bool
odd n = not (even n)
