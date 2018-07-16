/- 
Copyright (c) 2018 Blair Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard, Blair Shi

This file is inspired by Johannes Hölzl's implementation of linear algebra in mathlib.

The thing we improved is this file descripes finite dimentional vector spaces
-/

import algebra.module -- for definition of vector_space  
import linear_algebra.basic -- for definition of is_basis 
import data.list.basic
universes u v 

class finite_dimensional_vector_space (k : Type u) (V : Type v) [field k] 
  extends vector_space k V :=
(ordered_basis : list V)
(is_ordered_basis : is_basis {v : V | v ∈ ordered_basis})

-- Now all we need is some theorems!

variables {k : Type u} {V : Type v}
variable [field k]
variables [ring k] [module k V]
variables (a : k) (b : V)
include k 

definition f_dimention
(k : Type u) (V : Type v) [field k] (fvs : finite_dimensional_vector_space k V) : ℕ :=
fvs.ordered_basis.length

def f_span (l : list V) : set V :=
span {vc : V | vc ∈ l}
 
def f_linear_independent (l : list V) : Prop := 
linear_independent {vc : V | vc ∈ l}


-- helper function to check whether two basis are equal
def are_basis_equal (l₀ : list V) (l₁ : list V) : Prop := 
∀vc : V, vc ∈ (f_span l₀) ∧ vc ∈ (f_span l₁) 

def is_basis_of_vecsp (l : list V) (fvs : finite_dimensional_vector_space k V) : Prop := 
(are_basis_equal l fvs.ordered_basis) ∧ (f_linear_independent l)

def is_in_vecsp (v : V) (fvs : finite_dimensional_vector_space k V) : Prop :=
v ∈ span {v₁ : V | v₁ ∈ fvs.ordered_basis}

section span_liid

variables (v₀ v₁ v₂ vc: V)
variables (l₀ l₁: list V)
variables (h₀ h₁ res₀ res₁ : Prop)
variable (fvs : finite_dimensional_vector_space k V)
-- 2.4
theorem linear_dependence_th (l : list V)
  (h₀ : ¬ (f_linear_independent l)) 
  (h₁ : (vc ∈ l) ∧ (vc ≠ (0:V))) 
  (h₂ : v₀ ∈ l ∧ v₀ ≠ vc)
  : (v₀ ∈ span {vr : V | vr ∈ l ∧ vr ≠ v₀}) 
  ∧ (span {vr : V | vr ∈ l ∧ vr ≠ v₀} = f_span l) := 
  begin
    let s : set V := {vr : V | vr ∈ l ∧ vr ≠ vc},
    split,
    sorry

  end
    -- apply exists.elim h₁,
    -- cases h₁ with vc hvc,
    -- cases hvc with hl hnz,
    -- let s : set V := {vr : V | vr ∈ l ∧ vr ≠ vc},
    --   have h₂ : vc ∈ span s,
    --       from 
    --       begin 
    --       apply exists.intro,
          -- apply and.intro,
          --   intro,
          --   intro h,
            -- def span (s : set β) : set β := { x | ∃(v : lc α β), (∀x∉s, v x = 0) ∧ x = v.sum (λb a, a • b) }
            -- lienar inde: ∀l : lc α β, (∀x∉s, l x = 0) → l.sum (λv c, c • v) = 0 → l = 0
  --         end,
            
            
  --     have h₃ : span s = f_span l,
  --       from 
  --         begin
  --           have h₅ : span s ⊆ f_span l, from sorry,

  --           have h₆ : f_span l ⊆ span s, from sorry,
  --           exact span s = f_span l, from h₅ h₆,

  --         end,
  --   intro,
  --   assume vc,
  --   apply exists.intro,
  --   apply and.intro,
  --   exact hl,
  --   apply and.intro,
  --   exact h₂,
  --   exact h₃,
  -- end
  
  
  

-- 2.5 In a finite-dimensional vector space, the length of 
-- every linearly independent list of vectors is less 
-- than or equal to the length of every spanning list of vectors.
theorem len_of_lide_le_dimention (fvs : finite_dimensional_vector_space k V) (l : list V) 
  (h₀ : f_linear_independent l)
  (h₁ : are_basis_equal l₀ fvs.ordered_basis)
  : l.length <= l₀.length := sorry

-- 2.8
theorem is_f_basis (l : list V) (fvs : finite_dimensional_vector_space k V):
  (∀ v₀, (is_in_vecsp v₀ fvs) ∧  (v₀ ∈ f_span l)) ↔ (is_basis_of_vecsp l fvs) := sorry 

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
  ∀l₀ , (are_basis_equal l₀ fvs.ordered_basis ∧ l₀.length = f_dimention k V fvs) 
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