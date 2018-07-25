import xenalib.Ellen_Arlt_matrix_rings algebra.group algebra.group_power init.algebra data.real.basic group_theory.subgroup data.complex.basic group_theory.coset

definition is_subgroup' {G : Type} [group G] (H : set G) := (1 : G) ∈ H ∧ (∀ g1 g2 : G, g1 ∈ H → g2 ∈ H → g1 * g2 ∈ H) ∧ 
∀ g : G, g ∈ H → g⁻¹ ∈ H 
theorem groups_Sheet1_Q1(G:Type)[group G]: ∀(x:G), x=1 ↔ x*x=x:=
begin
intro x, 
split ,
intro H1,
rw[H1],
exact mul_one 1,
intro H2,
have H3 : x*x =x*1,
rw[ mul_one x],
exact H2,
exact mul_left_cancel H3,
end
theorem groups_Sheet1_Q2a (G : Type) [group G] (H1 H2 : set G) : is_subgroup' H1 → is_subgroup' H2 → is_subgroup' (H1 ∩ H2) :=
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
variables {G : Type*} [group G]
variables (H1 H2 : set G)
--theorem groups_Sheet1_Q2b  : is_subgroup' H1 → is_subgroup' H2
def Real_excluding_neg_one: Type:= {x : ℝ  //  x ≠ -1}

instance : has_coe Real_excluding_neg_one ℝ := 
by unfold Real_excluding_neg_one; apply_instance

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

def mulR : Real_excluding_neg_one → Real_excluding_neg_one → Real_excluding_neg_one :=
λ x y, ⟨(x : ℝ) + y + x * y, begin
assume H1: (x:ℝ) +y + x*y = -1,
rw eq_neg_iff_add_eq_zero at H1,
have H2: (x:ℝ) + x*y +y+1=0,
rw[← H1], simp,
have H3: (x:ℝ) *(1 +y) + y+1=0,
rw[left_distrib],
rw[ mul_one (x:ℝ )],
exact H2,
have H4: ((x:ℝ) +1)*(1 +y) =0 ,
rw[right_distrib],
rw[ add_assoc] at H3,
rw[add_comm (y:ℝ ) 1] at H3,
rw[one_mul ],
exact H3,
have H5: (x:ℝ)+1 =0 ∨ 1+ (y:ℝ ) =0,
exact mul_eq_zero.1 H4,
cases H5,
have H6 : (x:ℝ) =-1,
rw[add_eq_zero_iff_eq_neg.1 H5],
exact x.2 H6,
have H7 : (y:ℝ) + 1 =0,
rw[add_comm],
exact H5,
have H8 : (y:ℝ) = -1,
rw[add_eq_zero_iff_eq_neg.1 H7],
exact y.2 H8,
 end⟩
 def invR: Real_excluding_neg_one → Real_excluding_neg_one:= λ x, ⟨ -(x:ℝ )*(x+1)⁻¹, begin
assume H1: - (x:ℝ )*(x+1)⁻¹  = -1,
have H2: (x:ℝ )+1 ≠ 0,
assume A1: (x:ℝ) +1 =0,
have A2: (x:ℝ ) =-1,
rw[add_eq_zero_iff_eq_neg.1 A1],
exact x.2 A2,
rw[← domain.mul_left_inj ( show (x:ℝ) +1  ≠  0, by exact H2 )] at H1,
rw[ mul_comm (-x:ℝ )  ((x + 1)⁻¹)] at H1,
rw[← mul_assoc] at H1,
rw[← div_eq_mul_inv] at H1,
--have A3 : (x:ℝ ) ≠ -1,
--exact x.2,
rw [div_self H2] at H1,
rw[right_distrib] at H1,
rw[one_mul] at H1,
rw[one_mul] at H1,
rw[mul_neg_one] at H1,
conv at H1 {to_lhs, rw [← add_zero (-x:ℝ )]},
have H2: (0:ℝ ) = -1,
exact add_left_cancel H1,
have H3: (0 :ℝ )≠ - 1,
norm_num,
exact H3 H2,
end⟩
definition D : group Real_excluding_neg_one  :=
{ mul := mulR,
 mul_assoc:= 
 begin 
intros a b c,
show mulR (mulR a b) c = mulR a (mulR b c),
unfold mulR,simp,ring,
end,
one:= ⟨ 0 , by norm_num⟩,
one_mul:= 
begin 
intro a,
unfold mulR,
simp,
end, 
mul_one:=
begin 
intro a,
show mulR a ⟨0, _⟩  = a,
unfold mulR,
simp,
end,
inv:= invR,
mul_left_inv :=
begin 
intro a,
show mulR (invR a) a = _,
unfold mulR,
unfold invR,
simp,
exact calc 

end

 

}



