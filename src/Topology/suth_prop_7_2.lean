import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space

universe u

open set filter lattice classical

#print definition set


#check empty 
def empty_set_topology : topological_space empty := 
{
is_open := λ (a : set empty),
true, is_open_univ := begin trivial, end,
is_open_inter := begin intros h1 h2 h3 h4, trivial end,
is_open_sUnion := begin intros h1 h2, trivial end
} 
#print univ
#check empty_set_topology.is_open 

#print set

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

theorem Proposition7_2 {α : Type u} {X : topological_space α} {U : set α} : X.is_open U ↔ ∀ x ∈ U, ∃ Ux : set α, Ux ⊆ U ∧ X.is_open Ux ∧ x ∈ Ux  := 
begin
split,
intro H1,
assume x,
intro H2,
existsi U,
exact ⟨subset.refl U, H1, H2⟩,

intro H1,
let S := {Ux : set α | Ux ⊆ U ∧ X.is_open Ux ∧  ∃ x: α ,  x ∈ Ux},

have Union : U = ⋃₀ S,
apply set.subset.antisymm_iff.2,
split,
swap,
apply set.sUnion_subset,
intros V H2,
rw set.mem_def at H2,
exact H2.left,
assume x,
intro x_in_U,
have H2 : (∃ (Ux : set α), Ux ⊆ U ∧ topological_space.is_open X Ux ∧  x ∈ Ux),
exact H1 x x_in_U,
cases H2 with Ux HUx,
rw set.mem_sUnion_eq,
existsi Ux,
have Ux_in_S : Ux ∈ S,
apply set.mem_def.2,
have : ∃ (x : α), x ∈ Ux,
existsi x,
exact HUx.right.right,
exact ⟨HUx.1, HUx.2.1, this⟩,
existsi Ux_in_S,
exact HUx.2.2,
rw Union,
have : (∀ V∈S, X.is_open V),
intros V H2,
rewrite set.mem_def at H2,
exact H2.2.1,
exact X.is_open_sUnion S this,
end

#print prefix set

--