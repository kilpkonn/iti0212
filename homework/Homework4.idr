{-                                                                              
    Tavo Annus                                                                    
    186060IAIB                                                                    
    Idris 2, version 0.3.0-3bbf52025                                              
-}                                                                              
module Homework4

import Data.Nat


%default total


public export
data  Even : (n : Nat) -> Type  where
	Z_even  :  Even Z
	SS_even :  Even n -> Even (S (S n))


public export
transport  :  {0 a : Type} -> (0 fiber : a -> Type) ->
	{0 x , y : a} -> (path : x = y) ->
	fiber x -> fiber y
transport fiber Refl  =  id


-- %hint
-- ss_even_helper : {n : Nat} -> Even (S (S (n + n))) -> Even (S n + S n)
-- ss_even_helper {n = n} proof = rewrite sym $ plusSuccRightSucc n n in proof


-- Problem 1
%hint
double_even : (n : Nat) -> Even (n + n)
double_even Z = Z_even
double_even (S n) = transport Even path lemma
  where
    lemma : Even $ S (S (n + n))
    lemma = SS_even $ double_even n
    path : S (S (n + n)) = (S n + S n)
    path = plusSuccRightSucc (S n) n
  -- ss_even_helper (SS_even (double_even n)) 

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
even_assoc_helper {n = n} {m = m} proof = transport Even path proof
  where
    path : ((n + n) + m * n) = (n + (n + m * n))
    path = sym $ plusAssociative n n (m * n)
  -- rewrite plusAssociative n n (m * n) in proof


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


-- Problem 4
Some  :  (a : Type) -> (p : a -> Type) -> Type
Some  =  DPair


%hint
plus_succ_right_helper : {n : Nat} -> n + n = m -> n + (S n) = S m
plus_succ_right_helper {n = n} Refl = sym (plusSuccRightSucc n n)
  -- rewrite plusSuccRightSucc n n in Refl


evens_are_doubles : Even n -> Some Nat $ \ m => m + m = n
evens_are_doubles Z_even = (Z ** Refl)
evens_are_doubles (SS_even even) = 
  let
    (x ** proof) = evens_are_doubles even
  in
    (S x **  cong S (plus_succ_right_helper proof))


-- Problem 5
half : (n : Nat) -> {auto even : Even n} -> Nat
half Z = Z
half (S (S n)) {even = SS_even even} = S $ half n


-- Problem 6
dec_not : {p : a -> Type} -> Dec (p x) -> Dec (Not $ p x)
dec_not (Yes prf) = No (\f => f prf)
dec_not (No contra) = Yes contra


dec_and : {p, q : a -> Type} -> Dec (p x) -> Dec (q x) -> Dec (p x `And` q x)
dec_and (Yes prf_a) (Yes prf_b) = Yes (prf_a, prf_b)
dec_and (Yes prf_a) (No contra_b) = No (\y => contra_b (snd y))
dec_and (No contra) dec_b = No (\y => contra (fst y))



