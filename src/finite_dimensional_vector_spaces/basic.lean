/- 
Copyright (c) 2018 Blair Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard, Blair Shi

This file is followed Linear Algebra Done Right and inspired by Johannes Hölzl's 
implementation of linear algebra in mathlib.

The thing we improved is this file describes finite dimentional vector spaces
-/

import algebra.module -- for definition of vector_space  
import linear_algebra.basic -- for definition of is_basis 
import data.list.basic
import analysis.real
universes u v 

class finite_dimensional_vector_space (k : Type u) (V : Type v) [field k] 
  extends vector_space k V :=
(ordered_basis : list V)
(is_ordered_basis : is_basis {v : V | v ∈ ordered_basis})


variables {k : Type u} {V : Type v}
variable [field k]
variable [module k V]
variables {a : k} {b : V}
include k 

definition f_dimention
(k : Type u) (V : Type v) [field k] (fvs : finite_dimensional_vector_space k V) : ℕ :=
fvs.ordered_basis.length

def f_span (l : list V) : set V :=
span {vc : V | vc ∈ l}
 
def f_linear_independent (l : list V) : Prop := 
linear_independent {vc : V | vc ∈ l}

-- helper function to check whether two basis are equal
def are_span_the_same (l₀ : list V) (l₁ : list V) : Prop := 
∀vc : V, vc ∈ (f_span l₀) ∧ vc ∈ (f_span l₁) 

def is_basis_of_vecsp (l : list V) (fvs : finite_dimensional_vector_space k V) : Prop := 
(f_span l = f_span fvs.ordered_basis) ∧ (f_linear_independent l)

def is_in_vecsp (v : V) (fvs : finite_dimensional_vector_space k V) : Prop :=
v ∈ span {v₁ : V | v₁ ∈ fvs.ordered_basis}

section basic_property
variables (x y : V)
variable (fvs : finite_dimensional_vector_space k V)

end basic_property

section span_liid
variables (v₀ v₁ v₂ vc: V)
variables (l₀ l₁: list V)
variables (h₀ h₁ res₀ res₁ : Prop)
variable (fvs : finite_dimensional_vector_space k V)

-- 2.4
theorem linear_dependence_th (l : list V)
  (h₀ : ¬ (f_linear_independent l)) 
  (h₁ : (vc ∈ l) ∧ (vc ≠ (0:V))) 
  : ∃ v₀, (v₀ ∈ l) ∧ (v₀ ≠ vc) ∧ (v₀ ∈ span {vr : V | vr ∈ l ∧ vr ≠ v₀}) 
  ∧ (span {vr : V | vr ∈ l ∧ vr ≠ v₀} = f_span l) :=
  sorry
  -- begin
  --   apply exists.intro,
  --   split,
  --   intro v₀,
  --   assume h₂ : v₀ ∈ l ∧ v₀ ≠ vc,    
    

    
  --   -- ⟨finsupp.single v₀ 1, by simp [finsupp.sum_single_index, this] {contextual := tt}⟩
  --   sorry
    
  -- end
  
  
  

-- 2.5 In a finite-dimensional vector space, the length of 
-- every linearly independent list of vectors is less 
-- than or equal to the length of every spanning list of vectors.
theorem len_of_lide_le_dimention (fvs : finite_dimensional_vector_space k V) (l : list V) 
  (h₀ : f_linear_independent l ∧ f_span l ⊆ f_span fvs.ordered_basis)
  (h₁ : f_span l₀ = f_span fvs.ordered_basis)
  : l.length <= l₀.length := 
  -- begin
  sorry
  -- end

-- 2.8
theorem is_f_basis (l : list V) (fvs : finite_dimensional_vector_space k V):
  (∀ v₀, (is_in_vecsp v₀ fvs) ∧  (v₀ ∈ f_span l)) ↔ (is_basis_of_vecsp l fvs) := 
  sorry
  -- begin
  -- apply iff.intro,
  -- -- A -> B
  -- intro h,
  -- split,
  

  -- -- B -> A



  -- end 

-- 2.10 Every spanning list in a vector space can be reduced to a basis of the vector space.
theorem span_set_can_be_basis (fvs : finite_dimensional_vector_space k V) : 
  ∀l₀, (f_span l₀  = f_span fvs.ordered_basis) → ∃l₁ ⊆ l₀, is_basis_of_vecsp l₁ fvs := sorry

-- 2.12 Every linearly independent list of vectors in a finite-dimensional vector space 
-- can be extended to a basis of the vector space.
theorem liide_list_can_be_basis (fvs : finite_dimensional_vector_space k V) :
  ∀l₀, linear_independent {vc : V | vc ∈ l₀} → ∃l₁, is_basis_of_vecsp (l₀ ++ l₁) fvs := 
  begin
  sorry
  end

-- Any two bases of a finite-dimensional vector space have the same length.
theorem any_basis_have_len:
  ∀l₀ l₁, (is_basis_of_vecsp l₀ fvs) ∧ (is_basis_of_vecsp l₁ fvs) →
   (l₀.length = l₁.length) := sorry 

-- If V is finite dimensional, then every spanning list of vectors in V with length dim V is a basis of V.
theorem span_with_dim_is_basis:
  ∀l₀ , (are_span_the_same l₀ fvs.ordered_basis ∧ l₀.length = f_dimention k V fvs) 
  → is_basis_of_vecsp l₀ fvs := sorry

theorem liide_list_with_dim_is_basis:
  ∀(l₀ : list V) , (f_linear_independent l₀ ∧ l₀.length = f_dimention k V fvs) 
  → is_basis_of_vecsp l₀ fvs := sorry 



end span_liid

-- define subspace 

-- theorem: If V is finite dimensional and U is a subspace of V, then dimU ≤ dimV.

-- Proposition: Suppose V is finite dimensional and U is a subspace of V.
-- Then there is a subspace W of V such that V = U ⊕ W.

-- Theorem: If U1 and U2 are subspaces of a finite-dimensional vector space, then
-- dim(U1 +U2)=dimU1 +dimU2 −dim(U1 ∩U2).

-- 2.19 Proposition: Suppose V is finite dimensional and U1 , . . . , Um are subspaces of V such that
-- 2.20 V=U1+···+Um
-- 2.21 dimV =dimU1 +···+dimUm. Then V = U1 ⊕ · · · ⊕ Um.

-- define linear map 


-- ∀l : lc α β, (∀x∉s, l x = 0) → l.sum (λv c, c • v) = 0 → l = 0
-- variable α : Type
-- variable i : α 
-- theorem not_for_all (p q: α → Prop) (h : ¬ (∀x : α, p x → q x)) : 
-- ∃x : α, p x ∧ ¬ (q x) :=
-- begin
-- apply exists.intro,
-- split,
-- apply exists.elim ((p i) ∨ ¬ (p i)) 
-- end
