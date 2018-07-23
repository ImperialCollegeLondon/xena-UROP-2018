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

--Definition 9.9
definition topology_dense {α : Type u} [topological_space α] (s : set α) : Prop := closure s = univ

--Proposition 9.11
theorem continuous_iff_image_closure_subset_closure_image {α : Type u} {β : Type v} [topological_space α] [topological_space β] (f : α → β) :
continuous f ↔ ∀ s, f '' closure s ⊆ closure (f '' s) := 
begin
  split,
    intros Hf s,
    exact image_closure_subset_closure_image Hf,
  intros Hf,
  rw continuous_iff_is_closed,
  intros b Hb,
  let f_inv_b := f ⁻¹' (b),
  let f_f_inv_b := f '' f_inv_b,
  have H1 : f '' (closure f_inv_b) ⊆ closure (f '' f_inv_b), by exact Hf f_inv_b,
  have H2 : closure (f '' f_inv_b) ⊆ closure b, by exact closure_mono (set.image_preimage_subset f b),
  have H3 : closure b = b, by exact closure_eq_of_is_closed Hb,
  rw H3 at H2,
  have H4 : f '' (closure f_inv_b) ⊆ b := set.subset.trans H1 H2,
  have H5 : f ⁻¹' (f '' closure f_inv_b) ⊆ f ⁻¹' b := set.preimage_mono H4,
  have H6 : closure f_inv_b ⊆ f_inv_b := set.subset.trans (set.subset_preimage_image f (closure f_inv_b)) H5,
  exact closure_eq_iff_is_closed.1 (set.eq_of_subset_of_subset H6 subset_closure),
end

--Prooposition 9.13
lemma closure_sInter' {α : Type u} [topological_space α] {I : set (set α)} : 
closure (sInter I) ⊆ (⋂ (i ∈ I), closure i) := 
begin
  have H1 : ⋂₀ I ⊆ ⋂ (i ∈ I), closure i,
    apply subset_bInter,
    intros x Hx,
    exact subset.trans (sInter_subset_of_mem Hx) subset_closure,
  have H2 : is_closed (⋂ (i : set α) (H : i ∈ I), closure i),
    have H6 : (⋂ (i : set α) (H : i ∈ I), closure i) = ⋂ (i : I), closure i,
      apply set.ext,
      intro x, simp,
      split, intro Hx,
      intros i Hi,
      exact Hx i Hi,
      intro Hx,
      intros x_1 Hx_1,
      exact Hx x_1 Hx_1,


  have H7 : is_closed (⋂ (i : I), closure ↑i) := @is_closed_Inter α _ _ _ (λ (i : I), @is_closed_closure _ _ ↑i),
  rw ←H6 at H7,
  assumption,
    have H3 : closure ⋂₀ I ⊆ closure ⋂ (i ∈ I), closure i := closure_mono H1,

    have H4 : @closure α _ (⋂ (i ∈ I), closure i) = ⋂ (i ∈ I), closure i,
      apply closure_eq_of_is_closed,
      exact H2,
    rw H4 at H3,
    exact H3,  
end

#print Inter


--Corollary 9.21
lemma frontier_eq_frontier_compl {α : Type u} [topological_space α] {s : set α} : frontier s = frontier (-s) :=
begin
rw frontier_eq_closure_inter_closure, rw frontier_eq_closure_inter_closure, 
finish,
end
--What should I have done instead of finish??



