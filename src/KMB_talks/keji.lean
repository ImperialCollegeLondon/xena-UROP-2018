--import group_theory.subgroup 

definition is_subgroup' {G : Type} [group G] (H : set G) := (1 : G) ∈ H ∧ (∀ g1 g2 : G, g1 ∈ H → g2 ∈ H → g1 * g2 ∈ H) ∧ 
∀ g : G, g ∈ H → g⁻¹ ∈ H 

theorem Q1' (G : Type) [group G] (H1 H2 : set G) : is_subgroup' H1 → is_subgroup' H2 → is_subgroup' (H1 ∩ H2) :=
begin
intro P1,
intro P2,
split,
{ split,
  exact P1.left,
  exact P2.left,
},
split,
{ intros g1 g2 Q1 Q2,
  split,
  exact P1.right.left g1 g2 Q1.left Q2.left,
  exact P2.right.left g1 g2 Q1.right Q2.right
},
intros g Hg,
split,
exact P1.right.right g Hg.1,
exact P2.2.2 g Hg.2,
end 

#exit 


instance Q1 (G : Type) [group G] (H1 H2 : set G) [is_subgroup H1] [is_subgroup H2] :
is_submonoid (H1 ∩ H2) :=
{ one_mem := ⟨is_submonoid.one_mem H1,is_submonoid.one_mem H2⟩,
  mul_mem := λ a b Ha Hb,⟨(is_submonoid.mul_mem Ha.1 Hb.1 : a * b ∈ H1),(is_submonoid.mul_mem Ha.2 Hb.2 : a * b ∈ H2)⟩ 
} 

theorem Q1' (G : Type) [group G] (H1 H2 : set G) [is_subgroup H1] [is_subgroup H2] :
is_subgroup (H1 ∩ H2) :=
{
  inv_mem := λ a Ha,⟨is_subgroup.inv_mem Ha.left,is_subgroup.inv_mem Ha.right⟩
}



definition Q0 : add_group ℤ := by apply_instance

definition D : group ℤ :=
{ mul := λ x y, x + y,
  mul_assoc := add_assoc,
  one := 0,
  one_mul := zero_add,
  mul_one := add_zero,
  inv := λ x, -x,
  mul_left_inv := λ n, begin
    show -n + n = 0,
    exact neg_add_self n,
  end 
}



