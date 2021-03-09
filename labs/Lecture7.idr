{-- 
 -- ITI0212 Lecture week 7, 2021.03.08
 -- 
 -- Totality for Data and Codata
 --
 --}


module Lecture7

import Data.Stream


namespace nat
	-- Recall the inductive type of natural numbers:
	data  Nat' : Type  where
		Z  :  Nat'
		S  :  Nat' -> Nat'

-- Idris functions, including constructors,
-- evaluate their arguments eagerly.

-- So every `Nat` is a finite term, `S $ S $ ... S Z`
three  :  Nat
three  =  S (1 + 1)


-- What if we try to write a term that is not finite?
badNat  :  Nat
badNat  =  S badNat


-- A recursive function on an inductive type is called *Total*
-- if it is:
-- (1) covering
-- (2) terminating

-- * Coverage is easy to decide mechanically:
--   just check for all constructors.
-- * Termination is impossible to decide mechanically
--   (cf. the halting problem).

-- Idris uses a simple syntactic conservative approximation
-- to termination for recursive functions on inductive types:
-- each recursive call must be on a proper subterm.


-- the Fibonacci function:
fib  :  Nat -> Nat
fib Z  =  0
fib (S Z)  =  1
fib (S (S n))  =  fib n + fib (S n)


-- iterate a function n times:
public export
iterate  :  Nat -> (a -> a) -> a -> a
iterate Z f  =  id
iterate (S n) f  =  iterate n f . f


-- an infinite recursion:
public export
forever  :  a -> a
forever x  =  forever x




-- For many programming tasks (e.g. servers)
-- we don't want termination.

-- A Process should keep running indefinitely
-- until we shut it down.

-- We call such types "coinductive data types"
-- or "codata types" for short.

-- A term of a codata type may be finite or infinite.


-- In Idris we indicate that a term
-- is being used coinductively with the
-- type constructor** `Inf : Type -> Type`.

public export
data  CoNat : Type  where
	Zero  :  CoNat
	Succ  :  (n : Inf CoNat) -> CoNat


-- We get a term of type `Inf CoNat` by using the
-- term constructor** `Delay : a -> Inf a`.
--                      **This is not exactly true

one  :  CoNat
one  =  Succ $ Delay Zero


-- Idris can automatically insert `Delay`s for you:

two  :  CoNat
two  =  Succ one


-- total because recursion is on a subterm:
public export
coN  :  Nat -> CoNat
coN Z  =  Zero
coN (S n)  =  Succ $ coN n


-- Because a term of type `Inf a` is potentially infinite,
-- Idris does not evaluate inside a `Delay` until needed.

-- Evaluation within a `Delay` is forced by pattern matching,
-- which reveals the constructor form of a term (hnf).

-- So Idris evaluates a term of type `CoNat` only until it
-- discovers whether it is `Zero` or a `Succ (Delay ?n)`.

public export
infinity  :  CoNat
infinity  =  Succ infinity


-- pattern matching on a `CoNat` forces the outermost `Delay`:
public export
pred  :  CoNat -> CoNat
pred Zero  =  Zero
pred (Succ (Delay n))  =  n


still_infinity  :  CoNat
still_infinity  =  iterate 1000 pred infinity


-- A recursive function on a coinductive type is called *Total*
-- if it is:
-- (1) covering
-- (2) productive

-- Productive means that it will evaluate
-- to a (possibly `Delay`ed) result in finite time.
-- Like termination for inductive types,
-- this is generally undecidable.

-- Idris uses a simple syntactic conservative approximation
-- to productivity for recursive functions on coinductive types:
-- each recursive call must be "guarded" by a constructor,
-- and thus by a(n implicit) `Delay`.

-- the recursive call to `plus` is
-- guarded by the constructor `Succ`:
public export
plus : CoNat -> CoNat -> CoNat
plus Zero n  =  n
plus (Succ m) n  =  Succ $ plus m n


even_more_infinite  :  CoNat
even_more_infinite  =  infinity `plus` infinity


-- not total because recursion is not constructor-guarded:
public export
uncoN : CoNat -> Nat
uncoN Zero  =  Z
uncoN (Succ n)  =  S $ uncoN n


-- possible non-totality is infectious:
badNat'  :  Nat
badNat'  =  uncoN infinity


-- Warning:  in the current implementations of Idris,
-- productivity recognition is pretty fragile.
-- Each subterm of a codata type must be
-- an *immediate* constructor argument:

-- should be productive, but not recognized:
infinity'  :  CoNat
infinity'  =  Succ $ id infinity'


-- Termination recognition is currently also pretty fragile.
-- Non-termination is "infectious", as it should be.

-- recognized as possibly non-terminating by infection:
hangs  :  a -> a
hangs  =  iterate 1 forever


-- Evaluating total function on a total argument should be safe,
-- but Idris currently does not try to do this.

-- terminating, but not recognized:
stops  :  a -> a
stops  =  iterate 0 forever


-- If you want to help improve this, there could be
-- a Master's thesis in it for you.  :-)




namespace list
	-- Recall the type of finite sequences:
	data  List' : Type -> Type  where
		Nil  :  List' a
		(::)  :  a -> List' a -> List' a


-- The type of finite or infinite sequences:
public export
data  CoList : Type -> Type  where
	Nil  :  CoList a
	(::) : (x : a) -> (xs : Inf (CoList a)) -> CoList a


-- recognized as productive for `CoList Nat`:
public export
zeros  :  CoList Nat
zeros = 0 :: zeros


-- take a prefix of a `CoList`:
-- (recognized as terminating for `Nat`)
public export
take  :  Nat -> CoList a -> List a
take Z xs  =  []
take n []  =  []
take (S n) (x :: xs)  =  x :: take n xs


-- recognized as productive for `CoList b`:
public export
mapCoList  :  (a -> b) -> CoList a -> CoList b
mapCoList f []  =  []
mapCoList f (x :: xs)  =  f x :: mapCoList f xs


-- a concise idiomatic definition:
-- should be productive, but not recognized:
nats'  :  CoList Nat
nats'  =  0 :: mapCoList S nats'


-- Often, we can rewrite such definitions
-- so that Idris can recognize totality:
public export
nats  :  CoList Nat
nats  =  nats_from 0
	where
		nats_from : Nat -> CoList Nat
		nats_from n = n :: nats_from (S n)




-- The hailstone function:
--            ( n/2  if n is even
--  h (n)  =  <
--            ( 3n+1  if n is odd

-- (using `Integer`s because `Nat` arithmetic is slow.):
h  :  Integer -> Integer
h n  =  case  n `mod` 2 == 0  of
	True  =>  n `div` 2
	False  =>  (3 * n) + 1


-- The hailstone sequence:
--
--  hail (n)  =  [n , h (n) , h (h (n)) , ...]
--
-- We can stop if we ever reach 0 or 1,
-- because of the cycles (0) and (1 , 4 , 2)
hail  :  Integer -> CoList Integer
hail n  =
	case  n < 2  of
		True  =>  [n]
		False  =>  n :: hail (h n)


-- the hailstone sequence is finite for 17:
hail_seventeen  :  List Integer
hail_seventeen  =  take 13 $ hail 17

-- Currently, nobody knows whether
-- `hail n` is finite for every n.
-- 
-- Paul Erdإ‘s said about the Collatz conjecture:
-- "Mathematics may not be ready for such problems."
-- He also offered US$500 for its solution.
-- Jeffrey Lagarias stated in 2010 that the Collatz conjecture
-- "is an extraordinarily difficult problem,
-- completely out of reach of present day mathematics."
--                                    - Wikipedia




-- Sometimes we do know that a sequence of data
-- will be infinite.
-- In this case, we don't want a Nil constructor.

-- this is in the standard library as Prelude.Stream:
namespace stream
	data  Stream'  :  Type -> Type  where
		(::)  :  a -> Inf (Stream' a) -> Stream' a

-- The stream of natural numbers:
-- (written so that Idris recognizes productivity)
public export
natStream  :  Stream Nat
natStream  =  nats_from 0
	where
		nats_from  :  Nat -> Stream Nat
		nats_from n = n :: nats_from (S n)


-- We can efficiently compute fib n
-- if we know both fib n-1 and fib n-2.
--
-- So we construct a stream of (fib n , fib (S n)) pairs:
--
--   n:          0    1    2    3    4    5
--   --         --   --   --   --   --   --
--   fib n:      0    1    1    2    3    5 ...
---  fib Sn:     1    1    2    3    5    8 ...

fibStream  :  Stream (Pair Nat Nat)
fibStream =  (0 , 1) :: map next fibStream
	where
		next  :  Pair Nat Nat -> Pair Nat Nat
		next (fib_pp, fib_p)  =  (fib_p , fib_pp + fib_p)

-- not actually very fast due to the `Nat` arithmetic,
-- but relative to `fib` above:
fast_fib  :  Nat -> Nat
fast_fib n  =  (fst . head . drop n) fibStream

-- NTS: try 26

