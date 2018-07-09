import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space
import analysis.real

universe u

open set filter lattice classical


section Mario
---- Mario 
variables {α  : Type*} [topological_space α ] ( x y : α )

def I01 := {x : ℝ // 0 ≤ x ∧ x ≤ 1}


-- Has euclidean subspace topology 
instance : topological_space I01 := by unfold I01; apply_instance
instance : has_zero I01 := ⟨⟨0, le_refl _, zero_le_one⟩⟩
instance : has_one I01 := ⟨⟨1, zero_le_one, le_refl _⟩⟩

structure path {α} [topological_space α] (x y : α) :=
(to_fun : I01 → α)
(at_zero : to_fun 0 = x)
(at_one : to_fun 1 = y)
(cont : continuous to_fun)

instance {α} [topological_space α] (x y : α) : 
has_coe_to_fun (path x y) := ⟨_, path.to_fun⟩

#check @path.cont 

parameters x : α 
def phi1 := @path x y 


end Mario