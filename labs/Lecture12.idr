{-- 
 -- ITI0212 Lecture week 12, 2021.04.12
 -- 
 -- Inductive Equality
 --
 --}

module Lecture12

import Data.Vect
import Syntax.PreorderReasoning
-- In Idris 2 the contrib package is needed as a dependency.
-- This is specified in the package file Lecture12.ipkg.
--
-- For information on Idris pagkages, see:
--    https://idris2.readthedocs.io/en/latest/tutorial/packages.html
-- To include the contrib package at the REPL, use option --package:
--    idris2 --package contrib Lecture12


%default total  --  needed to ensure proof validity




{-  Equality as a Boolean-Valued Function  -}


is_equal  :  Nat -> Nat -> Bool
is_equal Z Z  =  True
is_equal Z (S n)  =  False
is_equal (S m) Z  =  False
is_equal (S m) (S n)  =  is_equal m n


-- "boolean blindness":

bounded_pred  :  Nat -> Nat
bounded_pred n with (is_equal 0 n)
	bounded_pred n | True  =  0
	bounded_pred n | False  =
		case  n  of -- Idris doesn't know n = S n' here
			Z  =>  0
			S n'  =>  n'

-- Idris doesn't know that if (is_equal 0 n) is False
-- then n must be a successor.




{-  Equality as an Indexed Type  -}

namespace equals
	data  Equal' : (x : a) -> (y : b) -> Type  where
		--  primitive evidence that anything is equal to itself:
		Refl'  :  Equal' x x


-- Idris 2 has  Equal  in the standard library
-- with syntactic sugar  (=), its name in Idris 1.

-- The only way to construct a term of type  Equal x y
-- is if the terms  (x : a)  and  (y : b)  are *computationally the same*.
-- This requires the types  a  and  b  be computationally the same too.


four_is_four  :  2 + 2 = 2 * 2
four_is_four  =  Refl


-- adding a zero on the left:
public export
plus_zero_left  :  {n : Nat} -> 0 + n = n
plus_zero_left  =  Refl


-- adding a successor on the left:
public export
plus_succ_left  :  {m , n : Nat} -> (S m) + n = S (m + n)
plus_succ_left  =  Refl




{--  On Dependent Pattern Matching  --}

-- A term of type  Equal x y  acts as
-- a proof that  x  and  y  are equal.

-- A context variable of type  Equal x y  acts as
-- an assumption that  x  and  y  are equal.

-- The only  Equal  constructor  Refl  has type  x = x,
-- so case analysis of an assumption of type  Equal x y
-- triggers the discovery that  x  and  y  must be the same.


namespace  scratch_1
	-- adding a zero on the right (naive version):
	private
	plus_zero_right  :  {n : Nat} -> n + 0 = n
	plus_zero_right {n = Z}  =  Refl
	plus_zero_right {n = S n}  =
		let
			IH  =  plus_zero_right {n = n}
		in
			succ_equal IH
		where
			succ_equal  :  i = j -> S i = S j
			succ_equal {i = k} Refl {j = k}  =  Refl

%hide plus_zero_right  --  so we can reuse the name


-- This succ_equal is pretty nice, but the proof didn't
-- depend on the type being  Nat  or the function being  S.
-- Let's generalize it to any type and any function.

-- Every function preserves equality:
public export
congruence  :  (0 f : a -> b) -> (path : x = y) -> f x = f y
congruence f Refl  =  Refl

-- Idris has a version of  congruence  in the standard library called  cong.
-- In Idris 1 the function  f  is inconveniently an implicit argument.

-- adding a zero on the right (streamlined version using cong):
%hint
public export
plus_zero_right  :  {n : Nat} -> n + 0 = n
plus_zero_right {n = Z}  =  Refl
plus_zero_right {n = S n}  =  cong S plus_zero_right


-- adding a successor on the right:
%hint
public export
plus_succ_right  :  {m , n : Nat} -> m + (S n) = S (m + n)
plus_succ_right {m = Z} {n = n}  =  Refl
plus_succ_right {m = S m} {n = n}  =  cong S plus_succ_right


-- There's a fair amount of computation happening here
-- and it can sometimes be hard to remember what's going on.
-- That may be fine for Idris, but it's not great for humans.


-- Let's establish some basic facts about equality
-- so that we can reason at a higher level of abstraction.


-- Equality is a symmetric relation:
symmetry  :  x = y -> y = x
symmetry Refl  =  Refl

-- Idris has a version of  symmetry  in the Prelude called  sym.


-- Equality is a transitive relation:
transitivity  :  from = via -> via = to -> from = to
transitivity Refl  =  id

-- Idris has a version of  transitivity  in the Prelude called  trans.



-- We can use  transitivity  to write equality proof
-- terms in a more human-friendly way,
-- by relying on algebra rather than computation.

namespace  scratch_2
	private
	-- symmetry of addition (using transitivity):
	plus_sym  :  {m , n : Nat} -> m + n = n + m
	plus_sym {m = Z} {n = n}  =  transitivity
		{from = Z + n}       plus_zero_left
		{via = n}            (sym plus_zero_right)
		{to = n + Z}
	plus_sym {m = S m} {n = n}  =  transitivity
		{from = S m + n}     plus_succ_left
		{via = S (m + n)}    $ transitivity (cong S plus_sym)
		{via = S (n + m)}    (sym plus_succ_right)
		{to = n + S m}

%hide plus_sym  --  so we can reuse the name



-- This is better but still pretty clunky.
-- Idris 1 includes a syntax extension mechanism
-- to make proofs like this more readable.
-- (see https://idris.readthedocs.io/en/latest/reference/misc.html#preorder-reasoning)
-- Unfortunately, it is not yet implemented in Idris 2.
-- Until it is, there is a work-around in the  contrib  package.
-- Both can be accessed by importing the module Syntax.PreorderReasoning.
-- In Idris 2, we need to tell it that we are using the  contrib  package
-- (see above).


-- symmetry of addition (using equational reasoning):
%hint
public export
plus_sym  :  {m , n : Nat} -> m + n = n + m
plus_sym {m = Z}  =  Calc $
	|~ Z + n
	~~ n          ...(plus_zero_left)
	~~ n + Z      ...(sym plus_zero_right)
plus_sym {m = S m}  =  Calc $
	|~ S m + n
	~~ S (m + n)  ...(plus_succ_left)
	~~ S (n + m)  ...(cong S plus_sym)
	~~ n + S m    ...(sym plus_succ_right)



-- associativity of addition (by induction on m):
%hint
public export
plus_assoc  :  {l , m , n : Nat} -> l + (m + n) = (l + m) + n
plus_assoc {m = Z}  =  Calc $
	|~ l + (Z + n)
	~~ l + n             ...(cong (l + ) plus_zero_left)
	~~ (l + Z) + n       ...(cong ( + n) $ sym plus_zero_right)
plus_assoc {m = S m}  =  Calc $
	|~ l + (S m + n)
	~~ l + S (m + n)     ...(cong (l + ) plus_succ_left)
	~~ S (l + (m + n))   ...(plus_succ_right)
	~~ S ((l + m) + n)   ...(cong S plus_assoc)
	~~ S(l + m) + n      ...(sym plus_succ_left)
	~~ (l + S m) + n     ...(cong ( + n) $ sym plus_succ_right)




{--  Equality of Types  --}


-- An indexed type is a function from the indexing type to Type.
-- So we can use conguence to turn an equality between indices
-- into an equality between types.

vect_length_sym  :  {m , n : Nat} -> Vect (m + n) a = Vect (n + m) a
vect_length_sym  =  cong (\ len => Vect len a) plus_sym



-- If we know that two types are equal
-- then we can write a coercion function between them:
public export
coerce  :  {0 a , b : Type} -> (path : a = b) -> a -> b
coerce  Refl  =  id



namespace  scratch_3
	private
	-- twisted Vect concatenation (using coerce):
	twisted_concat  :  {m , n : Nat} -> Vect m a -> Vect n a -> Vect (n + m) a
	twisted_concat xs ys  =  coerce vect_length_sym (xs ++ ys)

%hide twisted_concat  --  so we can reuse the name


-- This is a common pattern.
-- Idea:
-- (1) Congruence says:
--     if the indices are equal then the indexed types are equal.
-- (2) Coercion says:
--     if the indexed types are equal then there is a function between them.
--
-- Combining these is called "transport":
public export
transport  :  {0 a : Type} -> (0 fiber : a -> Type) ->
	{0 x , y : a} -> (path : x = y) ->
	fiber x -> fiber y
transport fiber Refl  =  id

{-
            fiber x                                 fiber y            
           _________                               _________           
          /         \                             /         \          
         /     p     \    transport fiber path   / transport \         
        |             |   ------------------->  |  fiber path |        
         \           /                           \     p     /         
          \_________/                             \_________/          
                                   path                                
               x    ===============================    y         : a   
                                                                       
 -}



-- Now we can write twisted vector concatenation as a one-liner:

-- twisted Vect concatenation (using transport):
twisted_concat  :  {m , n : Nat} -> Vect m a -> Vect n a -> Vect (n + m) a
twisted_concat xs ys  =  transport (\ len => Vect len a) plus_sym (xs ++ ys)

{-
        Vect (m + n) a                          Vect (n + m) a         
           _________                               _________           
          /         \     transport (Vect _ a)    /         \          
         /           \         plus_sym          /           \         
        |  xs ++ ys   |   ------------------->  |             |        
         \           /                           \           /         
          \_________/                             \_________/          
                               plus_sym                                
             m + n  ===============================  n + m       : Nat 
                                                                       
 -}


-- Idris has a version of  transport  in the standard library
-- called  Builtin.replace.
-- Inconveniently, it takes the type constructor
-- as an implicit argument called  p.

