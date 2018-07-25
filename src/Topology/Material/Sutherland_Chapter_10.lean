import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space

import Topology.Material.Sutherland_Chapter_8

import data.equiv.basic

local attribute [instance] classical.prop_decidable

universes u v w

open set filter lattice classical

-- Below is the definition of the subspace_topology
-- I think we should actually use the subspace topology already in lean 
-- It is the one induced by the inclusion map, subspace.val
-- It is called subtype.topological_space
def subspace_topology {α : Type u} [X : topological_space α] (A : set α) : topological_space A := {
  is_open := λ I, ∃ U : set α, X.is_open U ∧ subtype.val '' I = U ∩ A, 
  is_open_univ := begin existsi univ, split, exact X.is_open_univ, rw univ_inter, unfold set.image, simp, end,
  is_open_inter := begin 
    intros s t Hs Ht,
    cases Hs with Us HUs,
    cases Ht with Ut HUt,
    let Ust := Us ∩ Ut,
    existsi Ust,
    split,
      exact X.is_open_inter Us Ut HUs.1 HUt.1,
    have H1 : Ust ∩ A = (Us ∩ A) ∩ (Ut ∩ A),
      rw inter_right_comm Us A (Ut ∩ A),
      simp [inter_assoc],
    rw H1,
    rw [← HUs.2, ← HUt.2],
    rw set.image_inter,
    exact subtype.val_injective,
  end,
  is_open_sUnion := begin
    intros I HI,
    let Uset := {U : set α | topological_space.is_open X U ∧ ∃ t ∈ I, subtype.val '' t = U ∩ A},
    let Uunion := ⋃₀ Uset,
    existsi Uunion,
    split,
      have H1 : (∀ (t : set α), t ∈ Uset → is_open t),
        intros t Ht,
        exact Ht.1,
      exact is_open_sUnion H1,
    apply set.ext,
    intro x,
    split,
      swap,
      intro Hx,
      cases Hx with Hx1 Hx2,
      simp at Hx1,
      cases Hx1 with U HU,
      simp,
      existsi Hx2,
      cases HU with HU HxU,
      cases HU with HUopen HU,
      cases HU with t Ht,
      existsi t,
      apply and.intro Ht.1,
      rw ← preimage_image_eq t subtype.val_injective,
      show x ∈ subtype.val '' t,
      rw Ht.2,
      exact ⟨HxU,Hx2⟩,
    simp,
    intros Hx HxinU0I,
    cases HxinU0I with t Ht,
    split,
      swap,
      exact Hx,
    have Hnext := HI t Ht.1,
    cases Hnext with Unext HUnext,
    existsi Unext,
    split,
      apply and.intro HUnext.1,
      existsi t,
      exact ⟨Ht.1, HUnext.2⟩,
    have x_in_val_t : x ∈ subtype.val '' t,
      simp,
      existsi Hx,
      exact Ht.2,
    rw HUnext.2 at x_in_val_t,
    exact x_in_val_t.1,
  end,
}


--Proof of equivalence of definitions
theorem subspace_top_eq_subtype_top {α : Type u} [X : topological_space α] (A : set α) :
(subspace_topology A).is_open = (subtype.topological_space).is_open :=
begin
  dunfold subtype.topological_space,
  unfold topological_space.induced,
  simp,
  funext V,
  apply propext,
  split,
    intro HU,
    cases HU with U HU,
    existsi U,
    apply and.intro HU.1,
    have H0 : subtype.val ⁻¹' (subtype.val '' V) = subtype.val ⁻¹' (A ∩ U),
      rw HU.2,
      simp,
      apply inter_comm,
    have H1 : V = subtype.val ⁻¹' (A ∩ U),
      rw ← H0,
      rw preimage_image_eq,
      exact subtype.val_injective,
    rw H1,
    simp,
    have preimage_A_eq_univ : subtype.val ⁻¹' A = @univ (subtype A),
      apply set.ext,
      intro x,
      simp,
      exact x.2,
    rw preimage_A_eq_univ,
    apply univ_inter,
  intro HU,
  cases HU with U HU,
  existsi U,
  apply and.intro HU.1,
  have H0 :  subtype.val '' V = subtype.val '' (subtype.val ⁻¹' U), by rw HU.2,
  rw H0,
  apply set.ext,
  intro x,
  simp,
  split,
    intro Hx,
    cases Hx with a Ha,
    rw ← Ha.2.2,
    apply and.intro Ha.2.1,
    exact Ha.1,
  intro Hx,
  existsi x,
  exact ⟨Hx.2, Hx.1, refl x⟩, 
end

--Prop 10.4
theorem inclusion_cont_subtype_top {α : Type u} [X : topological_space α] (A : set α) : @continuous _ _ (subtype.topological_space) _ (λ (a : A), (a : α)) := 
begin
unfold continuous,
unfold is_open,
intros s Hs,
simp,
unfold subtype.topological_space,
unfold topological_space.induced,
simp,
existsi s,
apply and.intro Hs,
unfold coe,
unfold lift_t,
unfold has_lift_t.lift,
unfold coe_t,
unfold has_coe_t.coe,
unfold coe_b,
unfold has_coe.coe,
end


--Prop 10.4 but with subspace topology (I won't do any more with the subspace topology)
theorem inclusion_cont_subspace_top {α : Type u} [X : topological_space α] (A : set α) : @continuous _ _ (subspace_topology A) _ (λ (a : A), (a : α)) := 
begin
unfold continuous,
unfold is_open,
rw subspace_top_eq_subtype_top,
exact inclusion_cont_subtype_top A,
end

--Corollary 10.5
theorem restriction_cont {α : Type u} [X : topological_space α] {β : Type v} [Y : topological_space β]
(f : α → β) (H : continuous f) (A : set α) : continuous (λ (x : A), f x) := 
begin
  have H0 : (λ (x : A), f ↑x) = f ∘ (λ (a : A), (a : α)), by simp,
  rw H0,
  exact (continuous.comp (inclusion_cont_subtype_top A) H), 
end

--Proposition 10.6
theorem inclusion_comp_cont_iff_cont {α : Type*} [X : topological_space α] {A : set α} {γ : Type*} [Z : topological_space γ]
(g : γ → A) : continuous g ↔ continuous ((λ (a : A), (a : α)) ∘ g) :=
begin
  split,
    intro Hg,
    exact continuous.comp Hg (inclusion_cont_subtype_top A),
  simp,
  unfold continuous,
  unfold is_open,
  intro H_i_comp_g,
  intros V HV,
  unfold subtype.topological_space at HV,
  unfold topological_space.induced at HV,
  simp at HV,
  cases HV with U HU,
  have H1 := H_i_comp_g U HU.1,
  rw HU.2,
  exact H1,
end

--set_option pp.implicit true


--Proposition 10.8
theorem inclusion_comp_cont_iff_cont_to_subtype_top {α : Type u} [X : topological_space α] {A : set α} (Trandom : topological_space A) :
(∀ {γ : Type u} [Z : topological_space γ]
(g : γ → A), (@continuous γ ↥A Z _ g ↔ @continuous γ α Z _ ((λ (a : A), (a : α)) ∘ g))) ↔ Trandom.is_open = (subtype.topological_space).is_open :=
begin
  split,
    swap,
    { intros H _ _ _,
      rw ←(@inclusion_comp_cont_iff_cont _ _ _ _ Z g),
      unfold continuous,
      unfold is_open,
      rw H,
    },
  intro H,
  apply set.ext, intro V, split,
    swap,
    have H1 := (@H (↥A) Trandom (@id A)).1 id_map_continuous,
    intro HV,
    unfold subtype.topological_space at HV, unfold topological_space.induced at HV, simp at HV,
    cases HV with U HU,
    have H2 :  Trandom.is_open (subtype.val ⁻¹' U),
      simp at H1, unfold continuous at H1,
      exact H1 U HU.1,  
    rw ← HU.2 at H2, assumption,
  have H1 := (@H (↥A) subtype.topological_space (@id A)).2,
  simp at H1,
  intro HV,
  have H2 := H1 _,
     unfold continuous at H2,
  exact H2 V HV,
  
  
  unfold continuous, unfold is_open, intros s Hs, unfold subtype.topological_space, unfold topological_space.induced, simp, existsi s, apply and.intro Hs, trivial,  
end
--!!!!!! THIS AGAIN !!!!!!


--Product Topologies
def product_top {α : Type*} {β : Type*} (X : topological_space α) (Y : topological_space β) : topological_space (α × β) :=
{is_open := λ (W : set (α × β)), ∃ (I ⊆ { b : set (α × β) | ∃ (U : set α) (V : set β),
  is_open U ∧ is_open V ∧ b = set.prod U V}), W = ⋃₀ I,
  is_open_univ := begin 
    existsi {d : set (α × β) | d = set.prod univ univ},
    have H : set.subset {d : set (α × β) | d = set.prod univ univ} {b : set (α × β) | ∃ (U : set α) (V : set β), is_open U ∧ is_open V ∧   b = set.prod U V},
      simp,
      unfold set.subset,
      intros a Ha,
      rw mem_set_of_eq at Ha,
      rw Ha,
      simp,
      existsi univ,
      simp,
      existsi univ, simp,
    existsi H,
    simp,
    have H1 : {d : set (α × β) | d = univ} = {univ},
      apply set.ext,
      intro x, simp,
    rw H1,
    rw sUnion_singleton,
  end,
  is_open_inter := begin
    intros W1 W2 HW1 HW2,
    cases HW1 with I1 HI1, cases HI1 with HI1 HWI1,
    cases HW2 with I2 HI2, cases HI2 with HI2 HWI2,
    existsi {e : set (α × β) | ∃ (U ∈ I1) (V ∈ I2), e = U ∩ V},
    have H : set.subset
        {e : set (α × β) | ∃ (U : set (α × β)) (H : U ∈ I1) (V : set (α × β)) (H : V ∈ I2), e = U ∩ V}
        {b : set (α × β) | ∃ (U : set α) (V : set β), is_open U ∧ is_open V ∧ b = set.prod U V},
      unfold set.subset,
      simp,
      intros a w1 Hw1 w2 Hw2 Ha,
      rw Ha,
      --U is going to be the intersection of the two open sets in X from each prod of w1 and w2.
      have H_form_w1 : ∃ (U : set α) (V : set β), is_open U ∧ is_open V ∧ w1 = set.prod U V,
        
        sorry,

    sorry,
    sorry,
  end,
  is_open_sUnion := sorry}

#print prefix set

-- I am not sure I like this definition because it doesn't always come from a union of opens, sometimes it will come from an intersection.
def product_top' {α : Type*} {β : Type*} (X : topological_space α) (Y : topological_space β) :  topological_space (α × β) :=
topological_space.generate_from (λ b , ∃ (U : set α) (V : set β), is_open U ∧ is_open V ∧ b = set.prod U V)

--Proposition 10.10
theorem left_proj_cont {α : Type*} {β : Type*} (X : topological_space α) (Y : topological_space β) 
: @continuous (α × β) α (product_top' X Y) X (λ p, p.1) :=
begin
  unfold continuous,
  unfold is_open,
  intros s Hs,
  simp,
  have H : prod.fst ⁻¹' s = (set.prod s (@univ β)),
    apply set.ext,
    intro x,
    simp,
  rw H,
  unfold product_top',
  unfold topological_space.generate_from,
  simp,
  sorry,  
end
variable α : Type u

#check (set (set (set α))) 