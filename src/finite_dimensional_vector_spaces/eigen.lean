import .linear_map .ring_n_is_module_of_vector
import xenalib.Ellen_Arlt_matrix_rings


-- eigenvalue and eigenvector

namespace eigen
open function

-- def smul {R : Type} {n : nat} [ring R] (s : R) (rn : has_space R n) : 
-- has_space R n := λ I, s * (rn I)

def has_space_to_vec {F : Type} {n : ℕ} (fn : has_space F n) :
vector F n := vector.of_fn fn

def mat_to_has_space {F : Type} {n : ℕ} [ring F] (M : matrix F n 1) :
has_space F n := λ I, M I 1


def smul' {F : Type} {n : ℕ} [ring F] (M : matrix F n n) (fn : has_space F n) :
has_space F n := @mat_to_has_space F n _ (map_matrix.mat_mul_vec M (has_space_to_vec fn))

def is_eigenvalue_M {F : Type*} {n : ℕ} [ring F] (M : matrix F n n ) (a : F) :=
∃ v : (has_space F n), (v ≠ (0 : has_space F n)) ∧ (smul' M v = smul a v)

def is_eigenvector_M {F : Type*} {n : ℕ} [ring F] (M : matrix F n n) (fn : has_space F n) :=
∃ a : F, smul' M fn = smul a fn

def is_eigenvalue {k : Type} {V : Type*} [field k] [vector_space k V] (T : linear_map V V) (a : k) :=
∃ v : V , (v ≠ (0 : V)) ∧ (T v = a • v)

def is_eigenvector {k : Type} {V : Type*} [field k] [vector_space k V] (T : linear_map V V) (v : V) (h : v ≠ (0 : V)) :=
∃ a : k, T v = a • v

-- #check @is_eigenvalue

-- A : matrix F n n
-- The eigenvalues of TA are just those of A. (TA : Fn → Fn,TA(v) = Av)

open vector

#print has_emptyc

instance (F : Type) (n : ℕ) [field F]: vector_space F (has_space F n) := 
{
  begin
    

  end
}

-- theorem eigen_map_equiv_one {F : Type} {n : ℕ} [field F] (M : matrix F n n) 
-- (T : linear_map (has_space F n) (has_space F n)) :
-- ∀ eva : F, is_eigenvalue_M M eva ↔ @is_eigenvalue F (has_space F n) _ _ F eva :=


-- Suppose V is a f.d.v.s, and B = {v1,...,vn} is a basis of V. Let T : V → V be a linear map.
-- i The eigenvalues of T are exactly the same as the eigenvalues of [T]B.
-- ii The eigenvectors of T are those v ∈ V such that [v]B is an eigenvector of [T]B.


-- theorem eigen_equiv_one (n : ℕ) (T : linear_map V V) (fvs : finite_dimensional_vector_space k V) :
-- ∀ eva : k, is_eigenvalue T eva → is_eigenvalue 

-- theorem eigen_equil_one (T : linear_map V V)  (b : vector_space.linear_map_to_vec):= sorry

-- Proposition 7.5. Suppose V is a f.d.v.s, and B = {v1, ..., vn} is a basis. Suppose T : V → V is a linear map. Then,
-- [T]B isdiagonal⇔v1,...,vn areeigenvectorsofT

-- Definition 7.6. If V is a f.d.v.s, and T : V → V is a linear map, say that T is diagonalisable if
-- there a basis of V consisting of eigenvectors of V .



-- Corollary 7.7. Suppose V is a f.d.v.s. with a basis B = {v1, ..., vn}. Suppose T : V → V is a
-- linear map. Then the following are equivalent: i T is diagonalisable
-- ii There is a basis C of V with [T]C is diagonal
-- iii There is an invertible n×n matrix P with P−1[T]BP a diagonal matrix
end eigen