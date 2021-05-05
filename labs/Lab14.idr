module Lab14

import Data.Nat
import Data.List
import Decidable.Equality
import Lecture11
import Lecture12
import Lecture13

%default total


%hint
uninhabited_is_empty : (empty : Uninhabited a) => Not a
uninhabited_is_empty = uninhabited


list_head : (xs : List a) -> {auto nonempty : Not (xs = [])} -> a
list_head [] = void $ nonempty Refl
list_head (x :: xs) = x 

%hint
lte_n_zero : LTE (S n) 0 -> Void
lte_n_zero LTEZero impossible
lte_n_zero (LTESucc x) impossible


list_index : (i : Nat) -> (xs : List a) -> 
             {auto inbounds : LTE (S i) (length xs)} -> a
list_index 0 (x :: xs) = x
list_index (S i) [] = void $ lte_n_zero inbounds
list_index (S i) (x :: xs) = list_index i xs {inbounds = lte_pred inbounds}


%hint
s_preserve_not_lte : Not (LTE m n) -> Not (LTE (S m) (S n))
s_preserve_not_lte f x = s_preserve_not_lte f x


decide_LTE : (m, n : Nat) -> Dec (LTE m n)
decide_LTE 0 0 = Yes $ LTEZero
decide_LTE 0 (S n) = Yes $ LTEZero
decide_LTE (S m) 0 = No $ lte_n_zero
decide_LTE (S m) (S n) = case decide_LTE m n of 
                              Yes m_lte_n => Yes $ LTESucc m_lte_n
                              No m_not_lte_n => No $ s_preserve_not_lte m_not_lte_n


Between : Nat -> Nat -> Nat -> Type
Between lower upper n = LTE lower n `And` LTE n upper


decide_between : (lower, upper, n : Nat) -> Dec (Between lower upper n)
decide_between lower upper n = 
   case decide_LTE lower n of
        Yes n_bigger_than_low => 
            case decide_LTE n upper of
                Yes n_smaller_than_upper => Yes (n_bigger_than_low, n_smaller_than_upper)
                No n_too_big => No $ n_too_big . snd
        No n_too_small => No $ n_too_small . fst


data Tree : Type -> Type where
  Leaf : Tree a
  Node : (l : Tree a) -> (x : a) -> (r : Tree a) -> Tree a


leaf_not_eq_node : Not (Leaf = (Tree a))
leaf_not_eq_node leaf_eq_tree  = ?leaf_not_eq_node_rhs


implementation Uninhabited (Leaf = (Tree a)) where
  uninhabited x = ?dfd


implementation DecEq a => DecEq (Tree a) where
  decEq Leaf Leaf = Yes Refl
  decEq Leaf (Node l x r) = No ?fdfd_4
  decEq (Node l x r) Leaf = No ?fdfd_3
  decEq (Node l x r) (Node y z w) = 
    case decEq x z of
       Yes x_z_eq => 
          case decEq l y of
              Yes l_tree_eq => 
                    case decEq r w of
                         Yes r_tree_eq => Yes ?sds
                         No r_differ => No ?fdfdfde
              No l_differ => ?fdfdf
       No x_not_eq_z => ?fdfd_5





