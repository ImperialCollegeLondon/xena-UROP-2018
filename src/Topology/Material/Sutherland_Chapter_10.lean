import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space

import data.equiv.basic

local attribute [instance] classical.prop_decidable

universes u v w

open set filter lattice classical

definition is_open_sets {α : Type u} (is_open : set α → Prop) :=
  is_open univ ∧ (∀s t, is_open s → is_open t → is_open (s ∩ t)) ∧ (∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))

definition is_to_top {α : Type u} (is_open : set α → Prop) (H : is_open_sets (is_open)) : topological_space α :=
{ is_open := is_open,
  is_open_univ := H.left,
  is_open_inter := H.right.left,
  is_open_sUnion := H.right.right
}

definition top_to_is {α : Type u} (T : topological_space α) : is_open_sets (T.is_open) :=
⟨T.is_open_univ,T.is_open_inter,T.is_open_sUnion⟩


-- Do this the sutherland way, then make a proof that it is equivalent to the lean way 
--Proof 3?? What on earth, subtype.val_injective????
def subspace_topology {α : Type u} [X : topological_space α] (A : set α) : topological_space A := {
  is_open := λ I, ∃ U : set α, X.is_open U ∧ subtype.val '' I = U ∩ A, 
  is_open_univ := begin existsi univ, split, exact X.is_open_univ, rw univ_inter, unfold set.image, simp, end,
  is_open_inter := begin 
    intros s t Hs Ht,
    cases Hs with Us HUs,
    cases Ht with Ut HUt,
    let Ust := Us ∩ Ut,
    existsi Ust,
    split,
      exact X.is_open_inter Us Ut HUs.1 HUt.1,
    have H1 : Ust ∩ A = (Us ∩ A) ∩ (Ut ∩ A),
      rw inter_right_comm Us A (Ut ∩ A),
      simp [inter_assoc],
    rw H1,
    rw [← HUs.2, ← HUt.2],
    rw set.image_inter,
    exact subtype.val_injective,
  end,
  is_open_sUnion := begin
    intros I HI,
    sorry,
    --let Uunion := ⋃ 
  end,
}
#print Union
#print prefix set
variable α : Type u
#check (set α)
#print set 
#print subtype.val