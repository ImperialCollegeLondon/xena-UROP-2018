/-
Copyright (c) 2018 Keji Neri, Blair Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blair Shi

-- This file aims to prove some theorems about eigenvalue and eigenvectors

* `is_eigenvalue` `is_eigenvector`: constructed eigenvalues and eigenvectors 
in terms of linear map way

* `is_eigenvalue_M` `is_eigenvector_M`: constructed eigenvalues and eigenvectors 
in terms of matrix way

-- Proved two ways are equivalent

* `is_diagonal_mat` : checked whether the given matrix is diagonal

-- currently working on Cayley-Hamilton Theorem 
- Proved e • V = (e • I) * V, with e : F, V : vector F
-/

import .linear_map .ring_n_is_module_of_vector
import xenalib.Ellen_Arlt_matrix_rings
import xenalib.Keji_further_matrix_things

namespace M_module
instance mo {R : Type} {n : ℕ} [ring R] : module R (matrix R n 1) :=
{
  smul_add := @smul_add' _ _ 1 _,
  add_smul := @add_smul' _ _ 1 _,
  mul_smul := @mul_smul' _ _ 1 _,
  one_smul := @one_smul' _ _ 1 _,
}
end M_module

def mat_to_has_space {F : Type} {n : ℕ} [ring F] (M : matrix F n 1) :
has_space F n := λ I, M I 0

def has_space_to_vec {F : Type} {n : ℕ} (fn : has_space F n) :
vector F n := vector.of_fn fn

instance add_hommm {F : Type} [ring F] {n : nat}   
: is_add_group_hom (@mat_to_has_space F n _) :=
{
  add :=
  begin
    intros a b,
    unfold mat_to_has_space,refl,
  end
}

def module_hom_mat_to_has_space {F : Type} [ring F] {n : nat} 
  : is_linear_map (@mat_to_has_space F n _) :=
{ 
  smul := 
  begin
    intro c,
    intro x,
    unfold mat_to_has_space,
    funext,
    refl,
  end,
  .. add_hommm
}

def mat_to_has_space_is_linear {F : Type} [ring F] {n : nat}:
linear_map (matrix F n 1) (has_space F n) :=
⟨mat_to_has_space, module_hom_mat_to_has_space⟩ 

def smul' {F : Type} {n : ℕ} [ring F] (M : matrix F n n) (fn : has_space F n) :
has_space F n := @mat_to_has_space_is_linear F _ n (map_matrix.mat_mul_vec M (has_space_to_vec fn))

theorem vector.nth_map {α β : Type*} {n : ℕ} (v : vector α n) (f : α → β) (m : fin n) :
  (v.map f).nth m = f (v.nth m) := 
begin
  cases v with l hl,
  unfold vector.nth vector.map,
  rw list.nth_le_map,
end

open M_module

open map_matrix

lemma smul_eq_smul_two {F : Type} {n : ℕ} [ring F] (fn : has_space F n) :
∀ a : F, (smul a fn) = 
mat_to_has_space_is_linear.val
(@smul_M F _ _ _ a (vec_to_mat((has_space_to_vec fn)))) :=
begin
intro a,
unfold mat_to_has_space_is_linear,
simp,
unfold mat_to_has_space,
unfold smul,
funext,
unfold smul_M,
unfold vec_to_mat,
unfold has_space_to_vec,
simp,
end

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

namespace eigen
open function

-- def smul {R : Type} {n : nat} [ring R] (s : R) (rn : has_space R n) : 
-- has_space R n := λ I, s * (rn I)

theorem has_space_eq_vec {F : Type} [ring F] {n : nat} (fn : has_space F n) :
∀ K, fn K = vector.nth (@has_space_to_vec _ _ fn) K :=
begin
intro,
unfold has_space_to_vec,
simp,
end

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

-- A : matrix F n n
-- The eigenvalues of TA are just those of A. (TA : Fn → Fn,TA(v) = Av)

open vector

instance {F : Type} {n : ℕ} [field F]: vector_space F (has_space F n) := {}

open map_matrix

#check transpose_of_product

theorem eigen_map_equiv_one {F : Type} {n : ℕ} [field F] (M : matrix F n n) :
∀ eva : F, is_eigenvalue_M M eva ↔ 
@is_eigenvalue F n _ _ (@matrix_to_linear_map _ _ _ _ (Mᵀ)) eva :=
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
  unfold_coes at h₀_hr,
  unfold mat_to_has_space_is_linear at h₀_hr,
  simp at h₀_hr,
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
  unfold_coes,
  unfold mat_to_has_space_is_linear,
  simp,
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

end eigen

namespace Cayley_Hamilton

open eigen

theorem L0 {F : Type} [comm_ring F] {n : ℕ} (v : has_space F n):
∀ eva : F, smul_M eva (vec_to_mat (has_space_to_vec v)) = 
matrix.mul F (smul_M eva (matrix.identity_matrix F)) (vec_to_mat (has_space_to_vec v)) :=
begin
intro eva,
unfold smul_M,
unfold matrix.mul,
funext,
unfold matrix.identity_matrix,
unfold vec_to_mat,
unfold has_space_to_vec,
simp,
conv in ( _ * _ * _)
begin
  rw [mul_assoc],
end,
conv
begin
  to_rhs,
  rw [← finset.mul_sum],
end,
congr,
rw [← @finset.sum_single _ _ _ _ (λ (x : fin n), ite (I = x) 1 0 * v x) I _],
simp,
intro J,
intro h,
funext,
simp,
split_ifs,
simp,
apply false.elim,
contradiction,
simp,
end

lemma sub_eq_sub {R : Type} [ring R] {a b : ℕ} (A B : matrix R a b) :
A - B = matrix.sub R A B :=
begin
refl,
end

@[simp] lemma val_eq_coe {α β γ : Type*} [ring α] [module α β] [module α γ] 
  (f : linear_map β γ) : f.val = f := rfl

theorem L1 {R : Type} [comm_ring R] {n : ℕ} (M : matrix R n n) (v : has_space R n):
∀ eva : R, (smul' M v = smul eva v) ↔ 
smul' (matrix.sub R M (smul_M eva (@matrix.identity_matrix R _ n))) v = (0 : has_space R n) :=
begin
intro eva,
split,
intro h₀,
rw [← sub_eq_zero] at h₀,
unfold smul' at h₀,
unfold smul',
simp only [smul_eq_smul_two] at h₀,
unfold mat_mul_vec,
unfold mat_mul_vec at h₀,
rw val_eq_coe at h₀,
conv at h₀
begin
  to_lhs,
  rw ← @linear_map.map_sub _ _ _ _ _ _ (mat_to_has_space_is_linear) _ _,
end,
have h₁ : matrix.sub R (matrix.mul R M (vec_to_mat (has_space_to_vec v))) (smul_M eva (vec_to_mat (has_space_to_vec v)))
= matrix.mul R (matrix.sub R M (smul_M eva (matrix.identity_matrix R))) (vec_to_mat (has_space_to_vec v)),
  rw [← matrix.mul_sub_mul],
congr,
rw [L0],
conv at h₀ in (matrix.mul R M _ - smul_M eva _)
begin
  rw [sub_eq_sub],
  rw [h₁],
end,
exact h₀,

intro h₀,
rw [← sub_eq_zero],
unfold smul' at h₀,
unfold_coes at h₀,
unfold mat_mul_vec at h₀,
conv at h₀ in ((matrix.mul R (matrix.sub R _ _) _))
begin
  rw [← matrix.mul_sub_mul],
end,
unfold mat_to_has_space_is_linear at h₀,
simp at h₀,
have h₁ :   mat_to_has_space
      (matrix.sub R (matrix.mul R M (vec_to_mat (has_space_to_vec v)))
         (matrix.mul R (smul_M eva (matrix.identity_matrix R)) (vec_to_mat (has_space_to_vec v)))) =
    smul' M v - smul eva v,
    unfold smul',
    unfold smul,
    unfold mat_to_has_space,
    unfold_coes,
    unfold mat_to_has_space_is_linear,
    simp,
    unfold mat_to_has_space,
    unfold matrix.sub,
    unfold mat_mul_vec,
    simp,
    funext,
    congr,
    unfold matrix.mul,
    unfold vec_to_mat,
    unfold has_space_to_vec,
    simp,
    unfold smul_M,
    conv in (_ * _ * _)
    begin
      rw [mul_assoc],
    end,
    rw [← finset.mul_sum],
    congr,
    rw [eq_comm],
    unfold matrix.identity_matrix,
    rw [← @finset.sum_single _ _ _ _ (λ (x : fin n), ite (I = x) 1 0 * v x) I _],
    simp,
    intro J,
    intro h,
    funext,
    simp,
    split_ifs,
    simp,
    apply false.elim,
    contradiction,
    simp,
  rw [h₁] at h₀,
  exact h₀,  
end

-- noncomputable def det_grl {R : Type} [comm_ring R] : Π {n : ℕ} (M : matrix R (n + 1) (n + 1)) 
-- (a : fin (n + 1)), R 
-- | 0 M a := M 0 0
-- | (n + 1) M a :=
--   finset.sum finset.univ (λ (K : fin (n + 1)), M a K * 
-- (((-1) ^ (a.val + K.val)) * (λ b : fin n, @det_grl n (minor M a.val K.val) b)))

-- theorem det_grl_eq_det {R : Type} [comm_ring R] :
-- ∀ n : ℕ, ∀ M : matrix R (n + 1) (n + 1), ∀ a : fin (n + 1),
-- det_grl M a = det M := 
-- begin
-- intros n M a,
-- unfold det,
-- unfold det_grl,

-- end


theorem L3 {R : Type} [comm_ring R] {n : ℕ} :
∀ a : R,
smul_M a (@matrix.identity_matrix _ _ n) = λ I J, if I = J then a else 0 :=
begin
intro a,
unfold smul_M,
funext,
unfold matrix.identity_matrix,
split_ifs,
rw [mul_one],
rw [mul_zero],
end

#check equiv.perm

theorem L2 {R : Type} [comm_ring R] {n : ℕ} (M : matrix R (n + 1) (n + 1)) :
smul_M (det M) (@matrix.identity_matrix _ _ (n + 1)) = matrix.mul R M (adj M) :=
begin
rw [L3],
funext,
unfold matrix.mul,
split_ifs,
unfold adj,
unfold transpose,
unfold cofactor,
unfold_coes,
unfold det,
unfold minor,
funext,
sorry
end


theorem Cayley_Hamilton {R : Type} [comm_ring R] {n : ℕ} (M : matrix R n n) :
∀ eva : R, @det n R _ (matrix.sub R M (smul_M eva (@matrix.identity_matrix R _ n))) = 0 
↔ is_eigenvalue_M M eva :=
begin
intro,
split,
intro h₀,
show is_eigenvalue_M M eva,
sorry,

intro h₀,
unfold is_eigenvalue_M at h₀,
cases h₀ with v,
cases h₀_h with h₀_hl h₀_hl,
rw [L1] at h₀_hl,
sorry
end

end Cayley_Hamilton

namespace diagonal

def is_diagonal_mat {R : Type} [ring R] {n: ℕ} (M : matrix R n n) : Prop :=
∀ I J, (I ≠ J) → (M I J = 0)

-- Proposition 7.5. Suppose V is a f.d.v.s, and B = {v1, ..., vn} is a basis. 
-- Suppose T : V → V is a linear map. Then,
-- [T]B is diagonal⇔v1,...,vn are eigenvectors of T


-- theorem diagonal_eigen_basis {R : Type} [ring R] {a b : ℕ} (M : )

-- Definition 7.6. If V is a f.d.v.s, and T : V → V is a linear map, say that T is diagonalisable if
-- there a basis of V consisting of eigenvectors of V .


-- Corollary 7.7. Suppose V is a f.d.v.s. with a basis B = {v1, ..., vn}. Suppose T : V → V is a
-- linear map. Then the following are equivalent: i T is diagonalisable
-- ii There is a basis C of V with [T]C is diagonal
-- iii There is an invertible n×n matrix P with P−1[T]BP a diagonal matrix

end diagonal