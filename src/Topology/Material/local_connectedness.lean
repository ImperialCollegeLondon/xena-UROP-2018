import analysis.topology.topological_space
import analysis.topology.continuity
import data.set.basic
import logic.basic
import Topology.Material.connected_spaces 
import Topology.Material.WIP_Path_Homotopy 
import Topology.Material.path_connectedness

open set filter lattice classical
local attribute [instance] prop_decidable

universe u
variables {α : Type u} {β : Type u} 


-- Locally connected / path connected spaces

def is_loc_con_at [topological_space α] (x : α) : Prop :=
∀ U : set α, x ∈ U → is_open U → (∃ V : set α, is_connected V ∧ is_open V ∧ x ∈ V ∧ V ⊂ U)

lemma is_loc_con_lemma [topological_space α] {x : α} {U : set α} (H1 : x ∈ U) (H2 : is_open U)
(H3 : is_loc_con_at x) : ∃ V : set α, is_connected V ∧ is_open V ∧ x ∈ V ∧ V ⊂ U := H3 U H1 H2
 
class locally_connected_space α extends topological_space α :=
  (forall_loc_con_at : ∀ x : α, is_loc_con_at x)



def is_loc_pcon_at [topological_space α] (x : α) : Prop :=
∀ U : set α, x ∈ U → is_open U → (∃ V : set α, is_path_connected V ∧ is_open V ∧ x ∈ V ∧ V ⊂ U)

lemma is_loc_pcon_lemma [topological_space α] {x : α} {U : set α} (H1 : x ∈ U) (H2 : is_open U)
(H3 : is_loc_pcon_at x) : ∃ V : set α, is_path_connected V ∧ is_open V ∧ x ∈ V ∧ V ⊂ U := H3 U H1 H2

class locally_path_connected_space α extends topological_space α :=
  (forall_loc_con_at : ∀ x : α, is_loc_pcon_at x)



def set_of_pcon_to_point [topological_space α] (x : α) : set α := {y : α | ∃ f : I01 → α, is_path x y f}

lemma self_mem_set_of_pcon [topological_space α] {x : α} : x ∈ set_of_pcon_to_point x :=
by {unfold set_of_pcon_to_point, rw [mem_set_of_eq], exact exists_id_path x}

lemma set_of_pcon_nempty [topological_space α] {x : α} : set_of_pcon_to_point x ≠ ∅ :=
ne_empty_of_mem self_mem_set_of_pcon



lemma set_of_pcon_is_pcon [topological_space α] : ∀ x : α, is_path_connected (set_of_pcon_to_point x) :=
begin
  intro z, unfold is_path_connected, intros x y hx hy,
  apply exists.intro, admit
end


lemma exists_open_pcon [topological_space α] {x : α} (H : is_loc_pcon_at x) : 
∃ V : set α, is_open V ∧ is_path_connected V :=
begin
  unfold is_loc_pcon_at at H, admit
end








theorem loc_pcon_and_con_imp_pcon [connected_space α] (H1 : ∀ x : α, is_loc_pcon_at x) 
{t : α} : path_connected_space α :=
begin
  let S : α → set α := set_of_pcon_to_point,
  suffices h1 : ∀ x : α, is_clopen (S x),
    have h2 : ∀ x : α, S x = univ :=
      (assume x, or.elim ((assume x, connected_space.clopen_trivial (S x) (h1 x)) x) 
      (by simp) (assume a1, by exact absurd a1 set_of_pcon_nempty)),
    have h3 : ∀ x : α, ∃ y : α, y ∈ S x := (assume x, exists_mem_of_ne_empty set_of_pcon_nempty),
    have h4 : ∀ x : α, is_path_connected univ, 
      {intro x, rw [←h2], exact set_of_pcon_is_pcon x},
    exact path_connected_space.mk ((is_pcon_univ_iff_pcon _ ).mpr (h4 t)),

  intro x, split,

  have g1 : ∀ U : set α, is_open U → x ∈ U → (∀ u ∈ U, ∃ )
/-
  have g1 : ∃ U : set α, is_open U ∧ is_path_connected U,
    {}

  have g2 := (H1 x) (S x) self_mem_set_of_pcon,
  --self_mem_set_of_pcon
  -/
end

