{-                                                                              
    Tavo Annus                                                                    
    186060IAIB                                                                    
    Idris 2, version 0.3.0-3bbf52025                                              
-}                                                                              
module Homework4

import Data.Nat

import Syntax.PreorderReasoning

%default total


public export
data  Even : (n : Nat) -> Type  where
	Z_even  :  Even Z
	SS_even :  Even n -> Even (S (S n))


%hint
ss_even_helper : {n : Nat} -> Even (S (S (n + n))) -> Even (S n + S n)
ss_even_helper {n = n} proof = rewrite sym $ plusSuccRightSucc n n in proof


-- Problem 1
%hint
double_even : (n : Nat) -> Even (n + n)
double_even Z = Z_even
double_even (S n) = ss_even_helper (SS_even (double_even n)) 

{-
%hint
double_add_even : (n_even : Even n) -> (m_even : Even m) -> Even (n + m)
double_add_even Z_even m_even = m_even
double_add_even (SS_even n) m_even = SS_even (double_add_even n m_even)
-}

%hint
even_sum_helper : Even n -> Even m -> Even (n + m)
even_sum_helper Z_even m_even = m_even
even_sum_helper (SS_even x) m_even = SS_even (even_sum_helper x m_even)


%hint
even_assoc_helper : {n, m : Nat} -> Even ((n + n) + m * n) -> Even (n + (n + m * n))
even_assoc_helper {n = n} {m = m} proof = rewrite plusAssociative n n (m * n) in proof


-- Problem 2
even_times_any : (m, n : Nat) -> Even m -> Even (m * n)
even_times_any Z n even_times_any_is_even = even_times_any_is_even
even_times_any (S (S m)) n (SS_even even_times_any_is_even) = 
  let 
      IH = even_times_any m n even_times_any_is_even 
  in 
      even_assoc_helper $ even_sum_helper (double_even n) IH


-- Problem 3
And  :  (a : Type) -> (b : Type) -> Type
And  =  Pair

Or  :  (a : Type) -> (b : Type) -> Type
Or  =  Either

dm1 : Not a `Or` Not b -> Not (a `And` b)
dm1 (Left f) (x, y) = f x
dm1 (Right f) (x, y) = f y
 

dm2 : Not a `And` Not b -> Not (a `Or` b)
dm2 (f, g) (Left x) = f x
dm2 (f, g) (Right x) = g x





