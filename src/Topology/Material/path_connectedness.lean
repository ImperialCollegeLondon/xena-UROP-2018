import analysis.topology.topological_space
import analysis.topology.continuity
import data.set.basic
import logic.basic
import Topology.Material.connected_spaces 
import Topology.Material.WIP_Path_Homotopy 
import analysis.real

open set filter lattice classical
local attribute [instance] prop_decidable

universe u
variables {α : Type u} {β : Type u}

def closed_interval (a b : ℝ) : set ℝ := {x : ℝ | a ≤ x ∧ x ≤ b}
def open_interval (a b : ℝ) : set ℝ := {x : ℝ | a < x ∧ x < b}


--def is_connected_in_reals (s : set ℝ) [topological_space ℝ] : Prop :=
--is_open s ↔ ∃ a b, s = open_interval a b

def is_path_connected [topological_space α] : Prop := 
∀ x y : α, ∃ f : I01 → α, is_path x y f

class path_connected_space α extends topological_space α :=
(path_connectedness : ∀ x y : α, ∃ f : I01 → α, is_path x y f)


lemma I01_connected : connected_space I01 := sorry

lemma I01_no_sep (C : connected_space I01) : ∀ U V : set I01, 
is_open U ∧ is_open V → ¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅) := sorry



theorem path_connected_imp_connected [path_connected_space α] : connected_space α :=
begin 
  suffices H : ∀ U V : set α, is_open U ∧ is_open V → ¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅),
    by exact no_open_separation_to_connected H,
  intros U V Huv Hc, 
  have hx : ∃ x, x ∈ U := ne_empty_iff_exists_mem.mp Hc.2.2.1,
  have hy : ∃ y, y ∈ V := ne_empty_iff_exists_mem.mp Hc.2.2.2,
  cases hx with x hx, cases hy with y hy,
  have hf : ∃ f : I01 → α, is_path x y f := path_connected_space.path_connectedness x y,
  cases hf with f hp, unfold is_path at hp,
  have g1 : (f ⁻¹' U) ∪ (f ⁻¹' V) = univ, {rw [←preimage_union,Hc.1],simp},
  have g2 : (f ⁻¹' U) ∩ (f ⁻¹' V) = ∅, {rw [←preimage_inter,Hc.2.1],simp},
  have g3 : (f ⁻¹' U) ≠ ∅, 
    {have a1 := hp.1,
      have a2 : f 0 ∈ U, rwa a1, rw [←mem_preimage_eq] at a2,
      have a3 : ∃ a, a ∈ f ⁻¹' U, exact exists.intro 0 a2,
      show (f ⁻¹' U) ≠ ∅, from ne_empty_iff_exists_mem.mpr a3},
  have g4 : (f ⁻¹' V) ≠ ∅, 
    {have a1 := hp.2.1,
      have a2 : f 1 ∈ V, rwa a1, rw [←mem_preimage_eq] at a2,
      have a3 : ∃ a, a ∈ f ⁻¹' V, exact exists.intro 1 a2,
      show (f ⁻¹' V) ≠ ∅, from ne_empty_iff_exists_mem.mpr a3},
  have g5 : is_open (f ⁻¹' U) := hp.2.2 U Huv.1,
  have g6 : is_open (f ⁻¹' V) := hp.2.2 V Huv.2,
  have ha : (f ⁻¹' U) ∪ (f ⁻¹' V) = univ ∧ (f ⁻¹' U) ∩ (f ⁻¹' V) = ∅ ∧ (f ⁻¹' U) ≠ ∅ ∧ (f ⁻¹' V) ≠ ∅ 
    := ⟨g1,g2,g3,g4⟩, 
  have C : connected_space I01 := I01_connected,
  have b1 : ¬((f ⁻¹' U) ∪ (f ⁻¹' V) = univ ∧ (f ⁻¹' U) ∩ (f ⁻¹' V) = ∅ ∧ (f ⁻¹' U) ≠ ∅ ∧ (f ⁻¹' V) ≠ ∅)
    := I01_no_sep C (f ⁻¹' U) (f ⁻¹' V) ⟨g5,g6⟩,
  by exact absurd ha b1,
  end

