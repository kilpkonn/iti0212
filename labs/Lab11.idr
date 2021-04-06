module Lab11

import Data.Nat
import Lecture11


succ_larger : {n : Nat} -> LTE n (S n)
succ_larger {n = 0} = LTEZero
succ_larger {n = (S n)} = LTESucc succ_larger


lte_weaken_right : {m, n : Nat} -> LTE m n -> LTE m (S n)
lte_weaken_right m_lte_n = lte_trans m_lte_n succ_larger


lte_weaken_left : {m, n : Nat} -> LTE (S m) n -> LTE m n
lte_weaken_left m_lte_n = lte_trans succ_larger m_lte_n


zero_plus_right : (m, n : Nat) -> LTE (m + 0) (m + n)
zero_plus_right Z n = LTEZero
zero_plus_right (S k) n = LTESucc $ zero_plus_right k n


zero_plus_left : (m, n : Nat) -> LTE (0 + n) (m + n)
zero_plus_left 0 n = lte_refl
zero_plus_left (S m) n = let
                            IH = zero_plus_left m n
                         in 
                            lte_trans IH succ_larger


succ_plus_right : (m, n : Nat) -> LTE (m + n) (m + S n)
succ_plus_right 0 n = succ_larger
succ_plus_right (S k) n = let 
                            IH = succ_plus_right k n
                          in 
                            LTESucc $ IH


succ_plus_left : (m, n : Nat) -> LTE (m + n) (S m + n)
succ_plus_left 0 n = succ_larger
succ_plus_left (S k) n = let 
                            IH = succ_plus_left k n
                         in 
                            LTESucc $ IH


data Positive : Nat -> Type where
  One_positive : Positive (S Z)
  S_positive : Positive n -> Positive (S n)


even_times_one : Even n -> Even (n * 1)
even_times_one Z_even = Z_even 
even_times_one (SS_even even_n) = SS_even (even_times_one even_n)


pow_even_pos : Even m -> Positive n -> Even (power m n)
pow_even_pos even_m One_positive = even_times_one even_m
pow_even_pos even_m (S_positive pos_n) = let
                                            IH = pow_even_pos even_m pos_n
                                         in 
                                            even_times_even even_m IH



