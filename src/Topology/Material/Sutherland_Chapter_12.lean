import analysis.topology.topological_space
import analysis.topology.continuity
import data.set.basic
import logic.basic
import Topology.Material.connected_spaces 
import analysis.real
--import Topology.Material.Path_Homotopy 

open set filter lattice classical
local attribute [instance] prop_decidable

universe u
variables {α : Type u} {β : Type u}

-- Definition 12.1 TODO: Work out why this breaks??
theorem connected_if_nexists_cts [topological_space α] :
¬ (∃ f : α → bool, continuous f ∧ function.surjective f) → connected_space α := 
  by {intro h, simp at h, exact cts_to_discrete_to_connected h}


-- Definition 12.2
def is_partition [topological_space α] (A B : set α) : Prop := 
is_open A ∧ is_open B ∧ A ∪ B = univ ∧ A ∩ B = ∅ ∧ A ≠ ∅ ∧ B ≠ ∅  


-- Proposition 12.3 
theorem connected_def_no_partition [connected_space α] : 
¬(∃ A B : set α, is_partition A B) :=
begin
  intros hc, unfold is_partition at hc,
  have h1 : ∀ U V : set α, is_open U ∧ is_open V → ¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅), 
    exact connected_def_no_open_separation,
    show false, by exact exists.elim hc 
      (assume A a, by exact exists.elim a
        (assume B b, by exact absurd b.2.2 (h1 A B (and.intro b.1 b.2.1)))),
end

theorem no_partition_to_connected [topological_space α] :
¬(∃ A B : set α, is_partition A B) → connected_space α := 
begin
  intro H, simp at H, unfold is_partition at H, 
  have h1 : ∀ (x y : set α), is_open x ∧ is_open y →  
  ¬ (x ∪ y = univ ∧ x ∩ y = ∅ ∧ x ≠ ∅ ∧ y ≠ ∅),
    {intros x y a1, have a2 := H x y, 
    rw [not_and_distrib,not_and_distrib,or_iff_not_imp_left,not_not] at a2,
    have a3 := a2 a1.1, rw [or_iff_not_imp_left,not_not] at a3, by exact a3 a1.2},
  by exact no_open_separation_to_connected h1,
end


-- Corollary 12.4


-- Example 12.5 (a)
theorem discrete_space_admits_partition [discrete_space α] {x y : α} (H : x ≠ y) : 
∃ U V : set α, is_partition U V :=
begin
  unfold is_partition,
  have h1 : ∀ s : set α, s ∩ -s = ∅, {intro x, simp},
  have h2 : ∀ s : set α, s ∪ -s = univ, {intro x, simp},
  have h3 : ∀ s : set α, is_open s, {intro s, exact discrete_space.discreteness s}, 
  have h4 : (singleton x) ∩ -(singleton x) = ∅, {exact h1 (singleton x)},
  have h5 : (singleton x) ∪ -(singleton x) = univ, {exact h2 (singleton x)},
  have h6 : is_open (singleton x), {exact h3 (singleton x)},
  have h7 : is_open (-(singleton x)), {exact h3 (-(singleton x))}, 
  have h8 : (singleton x) ≠ ∅ := ne_empty_iff_exists_mem.mpr (exists.intro x (mem_singleton x)),
  have h9 : y ∈ (-(singleton x)), 
        {have b1 : y ∉ (singleton x), {by_contradiction hc, rw [mem_singleton_iff] at hc, 
        rw [eq_comm] at hc, exact absurd hc H}, exact (mem_compl_iff _ _ ).mpr b1},
  have h10 : -(singleton x) ≠ ∅ := ne_empty_iff_exists_mem.mpr (exists.intro y h9),
  have h11 : is_open (singleton x) ∧ is_open (-(singleton x)) ∧ (singleton x) ∪ -(singleton x) = univ ∧ 
  (singleton x) ∩ -(singleton x) = ∅ ∧ (singleton x) ≠ ∅ ∧ -(singleton x) ≠ ∅ := ⟨h6,h7,h5,h4,h8,h10⟩, 
  by exact exists.intro (singleton x) (by exact exists.intro (-(singleton x)) (h11)), 
end

-- Example 12.5 (b)
theorem indiscrete_space_admits_no_partition [indiscrete_space α] :
¬(∃ A B : set α, is_partition A B) :=
begin
  simp, intros A B hc, unfold is_partition at hc,
  show false, from absurd hc.1 (indiscrete_space.indiscreteness A),
end

-- Proposition 12.7

def interval (a b : ℝ) : set ℝ := {x : ℝ | a ≤ x ∧ x ≤ b}

lemma le_lt_trans {x y z : ℝ} (h1 : x ≤ y) (h2 : y < z) : x < z :=
begin
  have H : x ≤ z := le_trans h1 (lt_iff_le_and_ne.mp h2).1,
    {by_contradiction g1, simp at g1,
      have g2 := le_antisymm H g1, rw g2 at h1,
      exact absurd h2 (not_lt.mpr h1)},
end

lemma lt_le_trans {x y z : ℝ} (h1 : x < y) (h2 : y ≤ z) : x < z :=
begin
  have H : x ≤ z := le_trans (lt_iff_le_and_ne.mp h1).1 h2,
    {by_contradiction g1, simp at g1,
      have g2 := le_antisymm H g1, rw g2 at h1,
      exact absurd h1 (not_lt.mpr h2)},
end


theorem interval_iff {a b : ℝ} (S : set ℝ): S = interval a b ↔ 
∀ x y z : ℝ, x ∈ S ∧ y ∈ S ∧ (x < z) ∧ (z < y) → z ∈ S :=   
begin
  apply iff.intro, 
    intros hS x y z h1, rw interval at hS, 
    by_contradiction hz, rw hS at hz, simp at hz,
    have g1 := h1.1, have g2 := h1.2.1,
    rw hS at g1 g2, simp at g2 g1,
    have g3 := h1.2.2.1, have g4 := h1.2.2.2,
    have t1 : a < z := le_lt_trans g1.1 g3,
    have t2 : z < b := lt_le_trans g4 g2.2,
    have t3 : b < z := (hz (le_of_lt t1)),
    by exact absurd t3 (not_lt_of_lt t2),
  
  by sorry

end


-- Theorem 12.8
-- Example 12.9
-- Theorem 12.10
-- Proposition 12.11

/-
theorem [connected_space α] [topological_space β] {f : α → β} 
(hf : continuous f) (hs : function.surjective f) :
is_connected (f '' univ) := sorry
 

theorem [connected_space α] [topological_space β] {f : α → β} (hf : continuous f) :
is_connected (f '' univ) := 
begin
  rw is_connected, intros U V H1 HC, rw is_open_in_subspace at H1, by sorry
end 
-/

-- Corollary 12.12
-- Corollary 12.13
-- Corollary 12.14
-- Corollary 12.15
-- Proposition 12.16
-- Corollary 12.17

-- Theorem 12.18

theorem prod_connected_if_connected [connected_space α] [connected_space β] 
: connected_space (α × β) := sorry

theorem left_connected_if_prod_connected [connected_space (α × β)] 
: connected_space α := sorry 

theorem right_connected_if_prod_connected [connected_space (α × β)] 
: connected_space β := sorry

-- Proposition 12.19
theorem subset_closure_connected [topological_space α] {A B : set α}
(hc : is_connected A) (hs1 : A ⊆ B) (hs2 : B ⊆ closure A) : is_connected B :=
sorry

-- Definition 12.20
-- Definition 12.21
-- Example 12.22 (a)
-- Example 12.22 (b)
-- Proposition 12.23
-- Lemma 12.24
-- Proposition 12.25
