import xenalib.Ellen_Arlt_matrix_rings
import algebra.big_operators
import data.set.finite
import algebra.module 

-- reserve infix ` ^ `: 50


-- class has_map (R : Type) (n : nat) [ring R] := (char : nat → fin n → R)
-- infix ^ := has_map.char

-- R^n
definition has_space (R : Type) (n : nat) [ring R] := (fin n) → R

instance (R : Type) [ring R] (n : nat) : add_comm_group (has_space R n) := sorry 

instance (R : Type) [ring R] (n : nat) : module R (has_space R n) := sorry 


namespace map_matrix

definition matrix_to_map {R : Type} [ring R] {a b : nat} (M : matrix R a b) :
    (has_space R b) → (has_space R a) := sorry 

instance {R : Type} [ring R] {a b : nat} (M : matrix R a b) : is_add_group_hom (matrix_to_map M) := sorry 

instance {R : Type} [ring R] {a b : nat} (M : matrix R a b) : is_module_hom (matrix_to_map M) := sorry 


definition map_to_matrix {R : Type} [ring R] {a b : nat} 
(f : (has_space R b) → (has_space R a)) [is_module_hom f] : matrix R a b :=
    λ i j, sorry

instance (R : Type) [ring R] (a b : nat) : is_add_group_hom (@matrix_to_map R _ a b)

instance is_add_group_hom map_to_matrix -- needs fixing like above

#print matrix_to_map
#print map_to_matrix

theorem equiv_one (R : Type) [ring R] {a b : nat} (f : (has_space R b) → (has_space R a)):
   matrix_to_map (map_to_matrix f) = f := 
   begin
    apply funext,
    intro x,
    simp,
    have h₀ : has_space R a, from fM x,
    have h₁ : has_space R b, from f h₀,
    unfold fM
   end

theorem equiv_two (R : Type) [ring R] {a b : nat} (M : matrix R a b):
    map_to_matrix (matrix_to_map M) = M := 
   begin
    apply funext,
    intro x,
    simp,
    have h₀ : has_space R a, from fM x,
    have h₁ : has_space R b, from f h₀,
    unfold fM
   end

end map_matrix