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
  
  exact continuous_subtype_val,
end

--Product Topologies
def product_top {α : Type*} {β : Type*} (X : topological_space α) (Y : topological_space β) : topological_space (α × β) :=
{is_open := λ (W : set (α × β)), ∃ (I ⊆ { b : set (α × β) | ∃ (U : set α) (V : set β),
  is_open U ∧ is_open V ∧ b = set.prod U V}), W = ⋃₀ I,
  is_open_univ := begin 
    existsi {d : set (α × β) | d = set.prod univ univ},
    have H : set.subset {d : set (α × β) | d = set.prod univ univ} {b : set (α × β) | ∃ (U : set α) (V : set β), is_open U ∧ is_open V ∧   b = set.prod U V},
      rw univ_prod_univ,
      unfold set.subset,
      intros a Ha,
      rw mem_set_of_eq at Ha,
      rw Ha,
      existsi univ,
      existsi univ, apply and.intro is_open_univ, apply and.intro is_open_univ, rw univ_prod_univ,
    existsi H,
    rw univ_prod_univ,
    have H1 : {d : set (α × β) | d = univ} = {univ},
      apply set.ext,
      intro x, rw mem_set_of_eq, rw mem_singleton_iff,
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
      have H1 := HI1 Hw1, rw mem_set_of_eq at H1,
      have H2 := HI2 Hw2, rw mem_set_of_eq at H2,
      rcases H1 with ⟨U1, V1, HU1, HV1, H1UV⟩,
      rcases H2 with ⟨U2, V2, HU2, HV2, H2UV⟩, 
      existsi (U1 ∩ U2), apply and.intro (X.is_open_inter U1 U2 HU1 HU2),
      existsi (V1 ∩ V2), apply and.intro (Y.is_open_inter V1 V2 HV1 HV2),
      rw H1UV, rw H2UV,
      apply prod_inter_prod,
    existsi H,
    rw HWI1, rw HWI2,
    apply set.ext,
    intro x,
    rw mem_set_of_eq, unfold set.inter, rw mem_set_of_eq, unfold set.sUnion, rw mem_set_of_eq, rw mem_set_of_eq,
    split,
      intro Hx,
      rcases Hx with ⟨HU, V, HV1, HV2⟩, rcases HU with ⟨U, HU1, HU2⟩,
      existsi (U ∩ V),
      existsi _,
      exact ⟨HU2, HV2⟩,
      rw mem_set_of_eq,
      existsi [U, HU1, V, HV1],
      trivial,
    intro Hx,
    rcases Hx with ⟨a, Ha1, Ha2⟩, rw mem_set_of_eq at Ha1, rcases Ha1 with ⟨U, HU, V, HV, HUV⟩, 
    rw HUV at Ha2,
    split,
      existsi [U, HU],
      exact Ha2.1,
    existsi [V, HV],
    exact Ha2.2,
  end,
  is_open_sUnion := begin
    intros I2 HI2,
    let Iset := {I | set.subset I
      {b : set (α × β) | ∃ (U : set α) (V : set β), is_open U ∧ is_open V ∧ b = set.prod U V} ∧ (∃ t ∈ I2, t = ⋃₀ I)},
    existsi ⋃₀ Iset,
    existsi _,
    swap,
    intros x Hx,
    rw mem_set_of_eq at Hx, rcases Hx with ⟨a, Ha, Ha2⟩,
    rw mem_set_of_eq at Ha,
    exact Ha.1 Ha2,
    apply set.ext, intro s, simp,
    split,
      intro HW, rcases HW with ⟨W, HW, HW2⟩,
        have H := HI2 W HW,
        rcases H with ⟨IW, HIW, HIIW⟩,
        rw HIIW at HW2, rw mem_sUnion_eq at HW2, rcases HW2 with ⟨square, Hsquare, Hsquare_s⟩,
        existsi square, split, existsi IW, refine ⟨_, Hsquare⟩, rw HIIW at HW, refine ⟨_, HW⟩,
        have Hsame : {b : set (α × β) | ∃ (U : set α) (V : set β), is_open U ∧ is_open V ∧ b = set.prod U V} = {b : set (α × β) | ∃ (U : set α), is_open U ∧ ∃ (V : set β), is_open V ∧ b = set.prod U V},
          apply set.ext, intro x, simp,
        rw ←Hsame, exact HIW,
      exact Hsquare_s,
    intro HW, cases HW with W HW, cases HW with HW HsW, cases HW with I HI,
    existsi ⋃₀ I,
    refine ⟨HI.1.2, _⟩,
    rw mem_sUnion_eq,
    existsi W, existsi HI.2, exact HsW,
  end
}


--Product Topology Basis
definition product_top_basis {α : Type*} {β : Type*} (X : topological_space α) (Y : topological_space β) :
set (set (α × β)) := { b : set (α × β) | ∃ (U : set α) (V : set β),
  is_open U ∧ is_open V ∧ b = set.prod U V}

theorem is_basis_product_top_basis {α : Type*} {β : Type*} (X : topological_space α) (Y : topological_space β) :
@topological_space.is_topological_basis _ (product_top X Y) (product_top_basis X Y) :=
begin
  unfold topological_space.is_topological_basis, split,
    intros t1 Ht1 t2 Ht2 x Hx, unfold product_top_basis at Ht1, rw mem_set_of_eq at Ht1,
    unfold product_top_basis at Ht2, rw mem_set_of_eq at Ht2,
    rcases Ht1 with ⟨U1, V1, Ht1⟩, rcases Ht2 with ⟨U2, V2, Ht2⟩,
    existsi (set.prod (U1 ∩ U2) (V1 ∩ V2)),
    refine ⟨_,_⟩, 
    unfold product_top_basis, rw mem_set_of_eq, existsi [U1 ∩ U2, V1 ∩ V2],
    exact ⟨is_open_inter Ht1.1 Ht2.1, is_open_inter Ht1.2.1 Ht2.2.1, refl (set.prod (U1 ∩ U2) (V1 ∩ V2))⟩,
    rw mem_prod, cases Hx with Hx1 Hx2, rw Ht1.2.2 at Hx1, rw Ht2.2.2 at Hx2, rw mem_prod at Hx1, rw mem_prod at Hx2,
    refine ⟨⟨⟨Hx1.1,Hx2.1⟩,Hx1.2,Hx2.2⟩,_⟩,
    rw Ht1.2.2, rw Ht2.2.2, intros y Hy, rw mem_prod at Hy, split,
    exact ⟨Hy.1.1, Hy.2.1⟩,
  exact ⟨Hy.1.2, Hy.2.2⟩,
  split,
    apply eq_univ_of_univ_subset, apply subset_sUnion_of_mem,
    existsi [univ, univ], apply and.intro is_open_univ, apply and.intro is_open_univ,
    rw ← univ_prod_univ,
    unfold product_top, unfold topological_space.generate_from,
    apply topological_space_eq,
    apply set.ext, intro W, split,
      intro HW, rcases HW with ⟨open_rects_set, Hopen_rects_set, HW⟩,
      unfold product_top_basis, 
      rw HW,
      exact topological_space.generate_open.sUnion open_rects_set 
      (λ (s : set (α × β)) (H : s ∈ open_rects_set), 
      topological_space.generate_open.basic s (Hopen_rects_set H)),
   
    apply topological_space.generate_open.rec,
    --THIS IS THE CORRECT PATH
          intros s Hs,
          unfold product_top_basis at Hs,
          rcases Hs with ⟨U, V, HU, HV, HW⟩,
          existsi {set.prod U V},
          have H :  {set.prod U V} ⊆
              {b : set (α × β) | ∃ (U : set α) (V : set β), is_open U ∧ is_open V ∧ b = set.prod U V},
            intros s Hs, rw mem_singleton_iff at Hs, rw Hs,
            existsi [U, V],
            exact ⟨HU, HV, refl (set.prod U V)⟩,
          existsi H,
          rw sUnion_singleton,
          exact HW,
        existsi {univ},
        have H :  {univ} ⊆
              {b : set (α × β) | ∃ (U : set α) (V : set β), is_open U ∧ is_open V ∧ b = set.prod U V},
          intros UNI HUNI,
          existsi [univ, univ],
          rw mem_singleton_iff at HUNI, rw HUNI,
          apply and.intro is_open_univ, apply and.intro is_open_univ,
          exact eq.symm univ_prod_univ,
        existsi H,
        rw sUnion_singleton,
      intros s t Hs1 Ht1 Hs Ht,
      rcases Hs with ⟨Is, HIs, HsUnionIs⟩,
      rcases Ht with ⟨It, HIt, HsUnionIt⟩,
      apply is_open_inter,
        existsi [Is, HIs], assumption,
      existsi [It, HIt], assumption,
    intros I HI_gen_prod_top_bas HI_open_sets,
    -- WHat set do I need? The set that contains all open rectangles appearing in any element of I
    existsi { b : set (α × β) | (∃ (U : set α) (V : set β), 
             is_open U ∧ is_open V ∧ b = set.prod U V) ∧ ∃ s ∈ I, b ⊆ s},
    existsi _, swap,
      intros x Hx, rw mem_set_of_eq, rw mem_set_of_eq at Hx,
      cases Hx with Hx1 Hx2, exact Hx1,
    apply eq_of_subset_of_subset,
      intros x Hx,
      rw mem_sUnion_eq at Hx,
      rcases Hx with ⟨t, Ht, Hxt⟩,
 -- Need to existsi the open rectangle that x is in
      have H := HI_open_sets t Ht, cases H with It HIt, cases HIt with HIt HIt2,
      rw HIt2 at Hxt, rcases Hxt with ⟨rect,rectIt,xrect⟩,
      existsi rect, refine ⟨⟨HIt rectIt,_⟩, _⟩,
        existsi [t, Ht],
        rw HIt2, apply subset_sUnion_of_mem rectIt,
      exact xrect,
    apply sUnion_subset,
    intros t Ht,
    cases Ht, rcases Ht_right, cases Ht_right_h,
    apply subset.trans Ht_right_h_h (subset_sUnion_of_mem Ht_right_h_w),
end



--Proof that our definition of product top is equivalent to the instance built into mathlib.
theorem product_top_eq_induced_prod_top {α : Type*} {β : Type*} (X : topological_space α) (Y : topological_space β) :
product_top X Y = topological_space.induced prod.fst X ⊔ topological_space.induced prod.snd Y :=
begin
  apply topological_space_eq,
  unfold product_top, unfold lattice.has_sup.sup, unfold semilattice_sup.sup, unfold semilattice_sup_bot.sup,
  unfold bounded_lattice.sup, unfold complete_lattice.sup, unfold Inf, unfold has_Inf.Inf,
  simp only [exists_prop, mem_set_of_eq, not_and, and_imp],
  apply set.ext,
  intro U, split,
    intro HU, rcases HU with ⟨I_U,HI_U,HI_U2⟩,
    intros T HXT HYT,
    unfold has_le.le at HXT, unfold preorder.le at HXT, unfold partial_order.le at HXT, unfold has_le.le at HXT, unfold preorder.le at HXT, unfold has_le.le at HXT, unfold preorder.le at HXT, unfold partial_order.le at HXT, unfold order_bot.le at HXT, unfold bounded_lattice.le at HXT, unfold complete_lattice.le at HXT, unfold bounded_lattice.le at HXT,
    --THe following should be each prod U1 univ, prod univ V1 for all rectangles prod U1 V1 
    --in U. Then intersect each pair and union them.
    rw HI_U2,
    apply is_open_sUnion,
    intros rect Hrect,
    --Split rect into the intersection of prod U1 univ and prod univ V1
    have Hrect2 := HI_U Hrect,
    rcases Hrect2 with ⟨Urect,Vrect,HUrect,HVrect,HUrectVrect⟩,
    have HUrectuniv : topological_space.is_open T (set.prod Urect univ),
      apply HXT, existsi Urect, split,
        exact HUrect,
      unfold preimage,
      apply set.ext, intro x,
      rw mem_set_of_eq, rw mem_prod,
      rw and_iff_left, exact mem_univ _,
    have HunivVrect : topological_space.is_open T (set.prod univ Vrect),
      apply HYT, existsi Vrect, split,
        exact HVrect,
      unfold preimage,
      apply set.ext, intro x,
      rw mem_set_of_eq, rw mem_prod,
      rw and_iff_right, exact mem_univ _,
    have H_open_rect := T.is_open_inter _ _ HUrectuniv HunivVrect,
    have Hrect_prod : set.prod Urect univ ∩ set.prod univ Vrect = rect,
      rw prod_inter_prod,
      rw inter_univ, rw univ_inter, rw HUrectVrect,
    rw Hrect_prod at H_open_rect,
    exact H_open_rect,
  intro HU,
  have H := HU (product_top X Y),
  have HX : topological_space.induced prod.fst X ≤ product_top X Y,
    intros V HV, unfold topological_space.induced at HV, cases HV with S HS, cases HS with HS HV,
    unfold preimage at HV, rw HV,
    existsi {set.prod S univ}, existsi _, 
      rw sUnion_singleton, apply set.ext, intro x, rw mem_set_of_eq,rw mem_prod, rw and_iff_left, exact mem_univ _,
    intros x Hx, existsi S, existsi univ, exact ⟨HS, is_open_univ, mem_singleton_iff.1 Hx⟩,
  have HY :  topological_space.induced prod.snd Y ≤ product_top X Y,
    intros V HV, cases HV with S HS, cases HS with HS HV, unfold preimage at HV, rw HV,
    existsi {set.prod univ S}, existsi _,
      rw sUnion_singleton, apply set.ext, intro x, rw mem_set_of_eq, rw mem_prod, rw and_iff_right, exact mem_univ _,
    intros x Hx, existsi univ, existsi S, exact ⟨is_open_univ, HS, mem_singleton_iff.1 Hx⟩,
  have H1 := H HX HY, 
  unfold product_top at H1,
   simp only [exists_prop, mem_set_of_eq, not_and, and_imp] at H1,
  exact H1,
end

#print prefix set
--Proposition 10.10
theorem left_proj_cont {α : Type*} {β : Type*} (X : topological_space α) (Y : topological_space β) 
: @continuous (α × β) α (product_top X Y) X (λ p, p.1) :=
begin
  unfold continuous,
  unfold is_open,
  intros s Hs,
  unfold product_top,
  existsi {set.prod s (univ : set β)}, split,
    intros pre Hpre, rw mem_singleton_iff at Hpre, rw Hpre,
    rw mem_set_of_eq, existsi [s, univ], exact ⟨Hs, Y.is_open_univ, rfl⟩,
  apply set.ext, intro x, rw mem_preimage_eq, rw sUnion_singleton, rw mem_prod, 
  rw and_iff_left, exact mem_univ x.snd,
end

theorem right_proj_cont {α : Type*} {β : Type*} (X : topological_space α) (Y : topological_space β) 
: @continuous (α × β) β (product_top X Y) Y (λ p, p.2) :=
begin
  unfold continuous,
  unfold is_open,
  intros s Hs,
  unfold product_top,
  existsi {set.prod (univ : set α) s}, split,
    intros pre Hpre, rw @mem_singleton_iff at Hpre, rw Hpre,
    rw mem_set_of_eq, existsi [univ, s], exact ⟨X.is_open_univ, Hs, rfl⟩,
  apply set.ext, intro x, rw mem_preimage_eq, rw sUnion_singleton, rw mem_prod, 
  rw and_iff_right, exact mem_univ x.fst,
end

--set_option pp.implicit true
set_option trace.simplify.rewrite true 


theorem cont_iff_proj_cont {α : Type*} {β : Type*} {γ : Type*} (X : topological_space α) 
(Y : topological_space β) (Z : topological_space γ) (f : γ → (α × β)) :
@continuous _ _ Z (product_top X Y) f ↔ (continuous ((λ (p : α × β), p.2) ∘ f) ∧ continuous ((λ (p : α × β), p.1) ∘ f)) :=
begin
    split,
    intro Hf, split,
      exact @continuous.comp _ _ _ _ (product_top X Y) _ _ _ Hf (right_proj_cont X Y),
    exact @continuous.comp _ _ _ _ (product_top X Y) _ _ _ Hf (left_proj_cont X Y),
  intro Hf,
  apply continuous_basis_to_continuous,
  apply is_basis_product_top_basis,
  intro b,
  unfold product_top_basis at b, rename b b1,
  rcases b.property with ⟨U, V, HU, HV,HB⟩,
  cases Hf with Hfsnd Hffst,
  have Hsnd := Hfsnd V HV,
  have Hfst := Hffst U HU,
  have H1 := is_open_inter Hfst Hsnd,
  have EQ : (λ (p : α × β), p.fst) ∘ f ⁻¹' U ∩ (λ (p : α × β), p.snd) ∘ f ⁻¹' V = (f ⁻¹' ↑b),
    rw preimage_comp, rw @preimage_comp _ _ _  f (λ (p : α × β), p.snd) _,
    rw ← preimage_inter,
    have H2 : prod.fst ⁻¹' U = set.prod U univ,
      apply set.ext, intro x, split,
        intro Hx, rw mem_preimage_eq at Hx, split, exact Hx, exact @mem_univ β x.snd,
      intro Hx, rw mem_preimage_eq, exact Hx.1,
    rw H2,
    have H3 : prod.snd ⁻¹' V = set.prod univ V,
      apply set.ext, intro x, split,
        intro Hx, rw mem_preimage_eq at Hx, split, exact @mem_univ α x.fst, exact Hx,
      intro Hx, rw mem_preimage_eq, exact Hx.2,
    rw H3,
    rw prod_inter_prod,
    rw inter_univ, rw univ_inter, rw ← HB, 
    have H4 : b.val = ↑b,
      trivial,
    rw H4,
  rw ← EQ,
  exact H1,
end



