import algebra.module -- for definition of vector_space  
import linear_algebra.basic -- for definition of is_basis 
import data.list.basic
universes u v 

class finite_dimensional_vector_space (k : Type u) (V : Type v) [field k] 
  extends vector_space k V :=
(ordered_basis : list V)
(is_ordered_basis : is_basis {v : V | v ∈ ordered_basis})

-- Now all we need is some theorems!

definition f_dimention
(k : Type u) (V : Type v) [field k] [fvs : finite_dimensional_vector_space k V] : ℕ :=
fvs.ordered_basis.length

variables (k : Type u) (V : Type v)
variable [field k]
variables (a : k) (b : V)
include k

def f_span (l : list V) : set V :=
{x | ∃(vc : lc k V), (∀x∉l, vc x = 0) ∧ x = vc.sum (λb a, a • b)}

def f_linear_independent (l : list V) : Prop := 
linear_independent {vc : V | vc ∈ l}
-- ∀li : lc k V, (∀x∉l, li x = 0) → li.sum (λv c, c • v) = 0 → li = 0

def is_basis_of_vecsp (l : list V) (fvs : finite_dimensional_vector_space k V) : Prop := 
(f_span l = f_span fvs.ordered_basis) ∧ (f_linear_independent l)

def is_in_vecsp (v : V) (fvs : finite_dimensional_vector_space k V) : Prop :=
v ∈ span {v₁ : V | v₁ ∈ fvs.ordered_basis}

variables v₀ v₁ v₂ : V
variables l₀ l₁: list V
variable fvs : finite_dimensional_vector_space k V
-- 2.4
theorem linear_dependence_th (l : list V)
  (h₀ : ¬(f_linear_independent l)) 
  (h₁ : ∃vc ∈ l, (vc ≠ 0)) 
  (res₀  : v₀ ∈ span {vr : V | vr ∈ l ∧ vr ≠ v₀}) 
  (res₁ : ∀v₁ ∈ l, span {vr : V | vr ∈ l ∧ vr ≠ v₁} = f_span l): h₀ ∧ h₁ → (res₀  ∧ res₁) := sorry

-- 2.5 In a finite-dimensional vector space, the length of 
-- every linearly independent list of vectors is less 
-- than or equal to the length of every spanning list of vectors.
theorem len_of_lide_le_dimention (fvs : finite_dimensional_vector_space k V) (l : list V) 
  (h₀ : f_linear_independent l)
  (h₁ : f_span l₀ = f_span fvs.ordered_basis)
  (res₀ : l.length <= l₀.length) : h₀ ∧ h₁ → res₀ := sorry

-- 2.8
theorem is_f_basis (l : list V) (fvs : finite_dimensional_vector_space k V)
  (h₀ : ∀ v₀, (is_in_vecsp v₀ fvs) ∧  (v₀ ∈ f_span l))
  (h₁ : is_basis_of_vecsp l fvs) : h₀ ↔ h₁ := sorry 

-- 2.10 Every spanning list in a vector space can be reduced to a basis of the vector space.
theorem span_set_can_be_basis (fvs : finite_dimensional_vector_space k V) : 
  ∀l₀, (f_span l₀  = f_span fvs.ordered_basis) → ∃l₁ ⊆ l₀, is_basis_of_vecsp l₁ fvs := sorry

-- 2.12 Every linearly independent list of vectors in a finite- dimensional vector space can be extended to a basis of the vector space.
theorem liide_list_can_be_basis (fvs : finite_dimensional_vector_space k V) :
  ∀l₀, f_linear_independent l₀ → ∃l₁, is_basis_of_vecsp (l₀ ++ l₁) fvs := sorry


-- Any two bases of a finite-dimensional vector space have the same length.
theorem any_basis_same_length:
  ∀l₀ l₁, (h₀ : is_basis_of_vecsp l₀ fvs) ∧ (h1 : is_basis_of_vecsp l₁ fvs) → (res : l₀.length = l₁.length) := sorry 

-- If V is finite dimensional, then every spanning list of vectors in V with length dimV is a basis of V.
theorem span_with_dim_is_basis:
  ∀l₀ , (f_span l₀ = f_span fvs.ordered_basis ∧ l₀.length = f_dimention k V) → is_basis_of_vecsp l₀ fvs := sorry

theorem liide_list_with_dim_is_basis:
  ∀l₀ , (f_linear_independent l₀ ∧ l₀.length = f_dimention k V) → is_basis_of_vecsp l₀ fvs := sorry 



-- define subspace 

-- theorem: If V is finite dimensional and U is a subspace of V, then dimU ≤ dimV.

-- Proposition: Suppose V is finite dimensional and U is a subspace of V.
-- Then there is a subspace W of V such that V = U ⊕ W.

-- Theorem: If U1 and U2 are subspaces of a finite-dimensional vector space, then
-- dim(U1 +U2)=dimU1 +dimU2 −dim(U1 ∩U2).

-- 2.19 Proposition: Suppose V is finite dimensional and U1 , . . . , Um are subspaces of V such that
-- 2.20 V=U1+···+Um
-- 2.21 dimV =dimU1 +···+dimUm. Then V = U1 ⊕ · · · ⊕ Um.

-- linear map 