module Lab12

import Syntax.PreorderReasoning
import Data.Vect

import Lecture12


%default total

%hint
times_zero_left : (n : Nat) -> 0 * n = 0
times_zero_left n = Refl


%hint
times_zero_right : (n : Nat) -> n * 0 = 0
times_zero_right 0 = Refl
times_zero_right (S k) = times_zero_right k


times_zero_right' : (n : Nat) -> n * 0 = 0
times_zero_right' 0 = Refl
times_zero_right' (S n) = Calc $
                          |~ S n * 0
                          ~~ 0 + (n * 0) ...(Refl)
                          ~~ 0 + 0       ...(times_zero_right' n)
                          ~~ 0           ...(Refl)


%hint
times_succ_left : {m, n : Nat} -> (S m) * n = (m * n) + n
times_succ_left = plus_sym -- Lol, I guess it works


%hint
times_succ_right : {m, n : Nat} -> m * (S n) = m + (m * n)
times_succ_right {m = 0} = Refl
times_succ_right {m = (S m)} = 
                      Calc $
                      |~ S m * S n
                      ~~ (m * S n) + S n       ...(plus_sym)
                      ~~ (m + (m * n)) + S n   ...(cong (+ (S n)) times_succ_right)
                      ~~ S ((m + (m * n)) + n) ...(plus_succ_right)
                      ~~ S (m + (m * n) + n)   ...(Refl)
                      ~~ S (m + ((m * n) + n)) ...(cong (\x => S (x)) $ sym plus_assoc)
                      ~~ S m + ((m * n) + n)   ...(Refl)
                      ~~ S m + (S m * n)       ...(cong (\x => S (m + x)) plus_sym)


times_sym : {m, n : Nat} -> m * n = n * m
times_sym {m = 0} {n = n} = sym $ times_zero_right n 
times_sym {m = (S m)} = Calc $
                        |~ S m * n
                        ~~ (m * n) + n   ...(plus_sym)
                        ~~ (n * m) + n   ...(cong (+ n) times_sym)
                        ~~ n + (n * m)   ...(plus_sym)
                        ~~ n * S m       ...(sym times_succ_right)


double_length_vect : {n : Nat} -> Vect (2 * n) a = Vect (n + n) a
double_length_vect = cong (\len => (Vect len a)) $ cong (n + ) plus_zero_right


plus_one_right : {n : Nat} -> n + 1 = S n
plus_one_right {n = 0} = Refl
plus_one_right {n = (S k)} = cong S plus_one_right 


reverse_vect : {n : Nat} -> Vect n a -> Vect n a
reverse_vect [] = [] 
reverse_vect (x :: xs) = transport (\len => Vect len a) plus_one_right ((reverse_vect xs) ++ [x])





