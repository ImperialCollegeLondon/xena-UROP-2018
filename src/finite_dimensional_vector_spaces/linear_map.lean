import xenalib.Ellen_Arlt_matrix_rings
import algebra.big_operators
import data.set.finite
import algebra.module 
import data.finsupp

-- reserve infix ` ^ `: 50


-- class has_map (R : Type) (n : nat) [ring R] := (char : nat → fin n → R)
-- infix ^ := has_map.char

-- R^n
definition has_space (R : Type) (n : nat) [ring R] := (fin n) → R

definition smul {R : Type} {n : nat} [ring R] (s: R) (rn: has_space R n) :
    (fin n) → R := λ I, s * (rn I)

def add (R : Type) (n : nat) [ring R] := λ (a b :has_space R n), (λ i, (a i) +(b i))

theorem add__assoc {R : Type} {n : nat} [ring R] (a b c :(fin n) → R): 
add R n (add R n a b) c = add R n a (add R n b c):=
begin 
unfold add,
funext,
simp,
end

theorem add__comm {R : Type} {n : nat} [ring R] (a b :(fin n) → R):
 add R n a b = add R n b a :=
begin 
unfold add,
funext,
exact add_comm (a i) (b i),
end

def zero (R : Type) (n : nat) [ring R]: has_space R n := λ (i:fin n),(0 :R)
#check zero
theorem zero__add {R : Type} {n : nat} [ring R] (a:has_space R n): add R n (zero R n) a = a:=
begin 
unfold add,
funext,
unfold zero,
simp,
end

def neg (R : Type) (n : nat) [ring R]:= λ (a:has_space R n),(λ i, -(a i))
theorem add__left__neg {R : Type} {n : nat} [ring R] (a :has_space R n): add R n (neg R n a) a = zero R n:=
begin 
unfold add,
unfold zero,
funext,
unfold neg,
simp,
end 
def add__zero {R : Type} {n : nat} [ring R] (a :has_space R n): add R n a (zero R n) =a:=
begin
unfold add,
funext,
unfold zero,
simp,
end

instance (R : Type) [ring R] (n : nat) : add_comm_group (has_space R n) := 
{add:=add R n,
add_assoc := add__assoc,
zero := zero R n,
zero_add:= zero__add,
neg:=neg R n,
add_left_neg:= add__left__neg, 
add_zero:= add__zero ,
add_comm:= add__comm,
}


namespace R_module
variables (R : Type) (n : nat)
variables [ring R] [module R (has_space R n)]

theorem smul_add (s : R) (rn rm : has_space R n) : 
    smul s (add R n rn rm) = add R n (smul s rn) (smul s rm) := 
-- s • (rn + rm) = s • rn + s • rm 
    begin
      apply funext,
      intro,
      unfold smul add,
      apply mul_add,
    end 

theorem add_smul (s t : R) (rn: has_space R n): 
    smul (s + t) rn = add R n (smul s rn) (smul t rn) := 
    begin
      apply funext,
      intro,
      unfold smul add,
      apply add_mul,
    end

theorem mul_smul (s t : R) (rn : has_space R n): 
    smul (s * t) rn = smul s (smul t rn) :=
    begin
      apply funext,
      intro,
      unfold smul,
      apply mul_assoc,
    end

theorem one_smul (rn : has_space R n): 
    smul (1 : R) rn = rn :=
    begin
      apply funext,
      intro,
      unfold smul,
      apply one_mul,
    end
end R_module



instance (R : Type) (n : nat) [ring R] {s t : R} {rn rm : has_space R n} 
: module R (has_space R n) :=
{   
    smul_add := R_module.smul_add R n,
    add_smul := R_module.add_smul,
    mul_smul := R_module.mul_smul,
    one_smul := R_module.one_smul,
}



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
    unfold fM,
    sorry
   end

theorem equiv_two (R : Type) [ring R] {a b : nat} (M : matrix R a b):
    map_to_matrix (matrix_to_map M) = M := 
   begin
    apply funext,
    intro x,
    simp,
    have h₀ : has_space R a, from fM x,
    have h₁ : has_space R b, from f h₀,
    unfold fM,
    sorry
   end

end map_matrix