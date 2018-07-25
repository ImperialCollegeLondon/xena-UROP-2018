import xenalib.Ellen_Arlt_matrix_rings
import algebra.big_operators
import data.set.finite

-- reserve infix ` ^ `: 50


-- class has_map (R : Type) (n : nat) [ring R] := (char : nat → fin n → R)
-- infix ^ := has_map.char

-- R^n
definition has_space (R : Type) (n : nat) [ring R] := (fin n) → R

namespace map_matrix

definition matrix_to_map (R : Type) [ring R] {a b : nat} (M : matrix R a b) :=
    (has_space R b) → (has_space R a)

definition map_to_matrix (R : Type) [ring R] {a b : nat} (f : (has_space R b) → (has_space R a)) :=
    matrix R a b


#print matrix_to_map
#print map_to_matrix

theorem equiv (R : Type) [ring R] {a b : nat} (M : matrix R a b) 
  (f : has_space R a → has_space R b):
   f ∘ (matrix_to_map ) = id
  begin

  end
    

end map_matrix