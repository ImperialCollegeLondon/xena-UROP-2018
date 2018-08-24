import algebra.group data.set.basic group_theory.subgroup group_theory.quotient_group

open function quotient_group is_subgroup is_group_hom

universe u 
--Todo: prove the first isomorphism theorem

variables {G : Type*} {H : Type*} [group G] [group H] 
variables (N K : set G)
variables [is_subgroup N] [is_subgroup K]

-- introducing the group isomorphism
class is_group_isom (f : G → H) extends is_group_hom f : Prop :=
(group_bij : bijective f)

namespace is_group_isom

variables (f : G → H) [is_group_isom f]

def automorphism (f₁ : G → G) := is_group_isom f₁



theorem isomorphism_thm_one (φ : G → H) [is_group_hom φ] : 
injective φ → ∃ (f₂ : (quotient (ker φ)) → H), is_group_isom f₂ := 
begin
intros,
sorry,
end

end is_group_isom

class is_ring_isom {α : Type*} {β : Type*} [ring α] [ring β] (f : α → β) extends is_ring_hom f : Prop :=
(ring_bij : bijective f)

#print notation $
    -- s $ t means s(t) where s is a function, and t is the input. the reason this exists is because it has very low binding power, so you can evaluate t first, then s $ t, making it a better alternative to s(t)