-- Setup for doing the topology problem sheet 2 exercise 4

import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space

universe u

open set filter lattice classical

-- A function that checks if a collection is sets satisfies the axioms of a topology
definition is_open_sets {α : Type u} (is_open : set α → Prop) :=
  is_open univ ∧ (∀s t, is_open s → is_open t → is_open (s ∩ t)) ∧ (∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))

-- A function that converts a proof that a collection of sets satisfies the axioms of a topology into an actual topology (see the definition of a topology in mathlib)
definition is_to_top {α : Type u} (is_open : set α → Prop) (H : is_open_sets (is_open)) : topological_space α :=
{ is_open := is_open,
  is_open_univ := H.left,
  is_open_inter := H.right.left,
  is_open_sUnion := H.right.right
}

-- A function that converts a topology into a proof that the given collection of sets satisfies the axioms of a topology.
definition top_to_is {α : Type u} (T : topological_space α) : is_open_sets (T.is_open) :=
⟨T.is_open_univ,T.is_open_inter,T.is_open_sUnion⟩

-- A proof that given two collections of sets that satisfy the axioms of a topology, their intersection satisfies the axioms of a topology.
theorem exercisefoura {α : Type u} {T1_sets T2_sets : set α → Prop} : is_open_sets T1_sets → is_open_sets T2_sets → is_open_sets (λ (a : set α), and (T1_sets a) (T2_sets a) :=
begin
intros H1 H2,
unfold is_open_sets,
split,
exact ⟨H1.left, H2.left⟩,
split,
intros s t H3 H4,
exact ⟨H1.right.left s t H3.left H4.left, H2.right.left s t H3.right H4.right⟩,
intros I H3,
split,
have H4 : ∀ (t : set α), t ∈ I → T1_sets t,
intros A H5,
exact (H3 A H5).left,
exact H1.right.right I H4,
have H4 :  ∀ (t : set α), t ∈ I → T2_sets t,
intros A H5,
exact (H3 A H5).right,
exact H2.right.right I H4,
end
