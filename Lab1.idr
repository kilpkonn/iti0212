small : Integer
small = 7

large : Integer
large = small * 6

average : Double -> Double -> Double
average x y = (x + y) / 2

medium : Integer
medium = cast (average (cast small) (cast large))
medium = ?medium_rhs
