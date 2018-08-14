import .linear_map .ring_n_is_module_of_vector
import xenalib.Ellen_Arlt_matrix_rings
import xenalib.Keji_further_matrix_things


-- eigenvalue and eigenvector

namespace eigen
open function

-- def smul {R : Type} {n : nat} [ring R] (s : R) (rn : has_space R n) : 
-- has_space R n := λ I, s * (rn I)

def has_space_to_vec {F : Type} {n : ℕ} (fn : has_space F n) :
vector F n := vector.of_fn fn

theorem has_space_eq_vec {F : Type} [ring F] {n : nat} (fn : has_space F n) :
∀ K, fn K = vector.nth (@has_space_to_vec _ _ fn) K :=
begin
intro,
unfold has_space_to_vec,
simp,
end

def mat_to_has_space {F : Type} {n : ℕ} [ring F] (M : matrix F n 1) :
has_space F n := λ I, M I 0

def has_space_to_row_mat {F : Type} {n : ℕ} [ring F] (fn : has_space F n) :
matrix F 1 n := λ I, λ J, fn J

def has_space_to_col_mat {F : Type} {n : ℕ} [ring F] (fn : has_space F n) :
matrix F n 1 := λ I, λ J, fn I

theorem has_space_eq_col_mat {F : Type} [ring F] {n : nat} (fn : has_space F n) :
∀ K, fn K = (has_space_to_col_mat fn) K 0 :=
begin
intro,
unfold has_space_to_col_mat,
end

theorem has_space_eq_row_mat {F : Type} [ring F] {n : nat} (fn : has_space F n) :
∀ K, fn K = (has_space_to_row_mat fn) 0 K :=
begin
intro,
unfold has_space_to_row_mat,
end



def smul' {F : Type} {n : ℕ} [ring F] (M : matrix F n n) (fn : has_space F n) :
has_space F n := @mat_to_has_space F n _ (map_matrix.mat_mul_vec M (has_space_to_vec fn))

def is_eigenvalue_M {F : Type*} {n : ℕ} [ring F] (M : matrix F n n ) (a : F) :=
∃ v : (has_space F n), (v ≠ (0 : has_space F n)) ∧ (smul' M v = smul a v)

def is_eigenvector_M {F : Type*} {n : ℕ} [ring F] (M : matrix F n n) (fn : has_space F n) :=
∃ a : F, smul' M fn = smul a fn

def is_eigenvalue {F : Type*} {n : ℕ} [field F] [vector_space F (has_space F n)] 
(T : linear_map (has_space F n) (has_space F n)) (a : F) :=
∃ v : (has_space F n) , (v ≠ (0 : (has_space F n))) ∧ (T v = smul a v)

def is_eigenvector {F : Type*} {n : ℕ} [field F] [vector_space F (has_space F n)] 
(T : linear_map (has_space F n) (has_space F n)) (v : has_space F n) (h : v ≠ (0 : has_space F n)) :=
∃ a : F, T v = smul a v

-- #check @is_eigenvalue

-- A : matrix F n n
-- The eigenvalues of TA are just those of A. (TA : Fn → Fn,TA(v) = Av)

open vector


instance {F : Type} {n : ℕ} [field F]: vector_space F (has_space F n) := {}

open map_matrix

theorem eigen_map_equiv_one {F : Type} {n : ℕ} [field F] (M : matrix F n n) :
∀ eva : F, is_eigenvalue_M M eva ↔ @is_eigenvalue F n _ _ (@matrix_to_linear_map _ _ _ _ (Mᵀ)) eva :=
begin
intro,
split,
intro h₀,
unfold is_eigenvalue,
cases h₀ with v,
have h₁: v ≠ 0 ∧ (matrix_to_linear_map (Mᵀ)) v = smul eva v,
  cases h₀_h with h₀_hl h₀_hr,
  split,
  exact h₀_hl,
  unfold smul' at h₀_hr,
  unfold mat_to_has_space at h₀_hr,
  unfold map_matrix.mat_mul_vec at h₀_hr,
  unfold matrix.mul at h₀_hr,
  unfold map_matrix.vec_to_mat at h₀_hr,
  show (matrix_to_linear_map (Mᵀ)).1 v = smul eva v, 
    unfold matrix_to_linear_map,
    simp,
    unfold matrix_to_map,
    rw ←h₀_hr,
    funext,
    simp only [(has_space_eq_vec _ _).symm],
    -- conv
    -- begin
    --   to_lhs,
    conv in (v _ * (Mᵀ) _ i)
      begin
        rw [has_space_eq_row_mat v _],
      end,
    conv in (M i _ * v _ )
      begin
        rw [has_space_eq_col_mat v _],
      end,
    show (matrix.mul F (has_space_to_row_mat v) (Mᵀ)) 0 i = _,
    show _ = matrix.mul F M (has_space_to_col_mat v) i 0,
    show _ =(matrix.mul F M (has_space_to_col_mat v))ᵀ 0 i,
    rw [transpose_of_product],
    have h₂ : (has_space_to_row_mat v) = has_space_to_col_mat vᵀ,
      unfold has_space_to_row_mat,
      unfold has_space_to_col_mat,
      funext,
      rw [transpose],
    rw [h₂],
    existsi v,
    exact h₁,

intro h₀,
unfold is_eigenvalue at h₀,
unfold is_eigenvalue_M,
cases h₀ with v,
have h₁ : v ≠ 0 ∧ smul' M v = smul eva v,
  split,
  cases h₀_h with h₀_hl h₀_hr,
  exact h₀_hl,
  unfold smul',
  cases h₀_h with h₀_hl h₀_hr,
  unfold_coes at h₀_hr,
  unfold matrix_to_linear_map at h₀_hr, 
  simp at h₀_hr,
  unfold matrix_to_map at h₀_hr,
  unfold mat_to_has_space,
  unfold mat_mul_vec,
  unfold vec_to_mat,
  unfold matrix.mul,
  unfold has_space_to_vec,
  rw [← h₀_hr],
  funext,
  simp,
  conv in (v _ * (Mᵀ) _ I)
    begin
        rw [has_space_eq_row_mat v _],
      end,
    conv in (M I _ * v _ )
      begin
        rw [has_space_eq_col_mat v _],
      end,
  rw [eq_comm],
  show (matrix.mul F (has_space_to_row_mat v) (Mᵀ)) 0 I = _,
  show _ = matrix.mul F M (has_space_to_col_mat v) I 0,
  show _ =(matrix.mul F M (has_space_to_col_mat v))ᵀ 0 I,
  rw [transpose_of_product],
      have h₂ : (has_space_to_row_mat v) = has_space_to_col_mat vᵀ,
      unfold has_space_to_row_mat,
      unfold has_space_to_col_mat,
      funext,
      rw [transpose],
  rw [h₂],
  existsi v,
  exact h₁,
end


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