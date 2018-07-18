import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space

import data.equiv
-- import data.equiv.basic

local attribute [instance] classical.prop_decidable

universes u v w

open set filter lattice classical

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

structure homeomorphism {α : Type*} {β : Type*} (X : topological_space α) (Y : topological_space β) extends equiv α β :=
(to_is_continuous : continuous to_fun)
(from_is_continuous : continuous inv_fun)

definition is_homeomorphic_to {α : Type u} {β : Type v} (X :topological_space α) (Y : topological_space β) : Prop := nonempty (homeomorphism X Y)

lemma id_map_continuous {α : Type u} {X : topological_space α} : continuous (@id α) :=
begin
  intros s H1,
  exact H1,
end

lemma constant_map_is_continuous {α : Type u} {β : Type v} {X : topological_space α} {Y : topological_space β} {f : α → β} (H : (∃ (b : β), f = function.const α b)) : continuous f :=
begin
  unfold continuous,
  cases H with b Hb,
    rw Hb,
    intros s Hs,
    by_cases (b ∈ s),
    unfold set.preimage,
    unfold function.const,
    have H : {x : α | b ∈ s} = univ,
      apply set.ext,
      simp,
      intro,
      assumption,
    rw H,
    exact X.is_open_univ,
  unfold set.preimage,
  unfold function.const,
  have H : {x : α | b ∈ s} = ∅,
    apply set.ext,
    simp,
    intro,
    assumption,
  rw H,
  simp,
end

def indiscrete_topology (α : Type u) : topological_space α := {
  is_open := λ y, y = ∅ ∨ y = univ,
  is_open_univ := or.inr rfl,
  is_open_inter := begin 
    intros s t Hs Ht, 
    cases Hs with Hsempty Hsuniv;
      cases Ht with Htempty Htuniv,
          rw Hsempty, 
          simp, 
        rw Hsempty, 
        simp, 
      rw Htempty,
      simp, 
    rw [Hsuniv, Htuniv], 
    simp, 
  end,
  is_open_sUnion := begin 
    intros I HI, 
    by_cases ∃ t ∈ I, t = univ,
      cases h with U HU,
      cases HU with U_in_I U_is_univ, 
      apply or.inr, 
      rw U_is_univ at U_in_I, 
      exact set.eq_of_subset_of_subset (set.subset_univ ⋃₀ I) (set.subset_sUnion_of_mem U_in_I), 
      simp at h, 
      apply or.inl, 
      have HI2 : ∀ (t : set α), t ∈ I → t = ∅, 
      intros t Ht, 
      cases (HI t Ht), 
        assumption, 
      rw h_1 at Ht, 
      cc, 
    rw set.sUnion_eq_Union, 
    apply set.ext, 
    intro x, 
    simp, 
    intros t Ht, 
    rw (HI2 t Ht), 
    simp, 
  end
}

def discrete_topology (α : Type u) : topological_space α := {
  is_open := λ y, true,
  is_open_univ := trivial,
  is_open_inter := λ _ _ _ _, trivial,
  is_open_sUnion := λ _ _, trivial,
}

--get rid of mention of X??
lemma map_from_discrete_is_continuous {α : Type u} {β : Type v} [X : topological_space α] [Y : topological_space β] 
(H : X = indiscrete_topology α) (f : α → β) : continuous f := 
begin
  admit,
end

theorem smap_from_discrete_is_continuous {α : Type u} {β : Type v} {X : topological_space α} {Y : topological_space β}
{H : X = indiscrete_topology α} (f : α → β) : continuous f :=  map_from_discrete_is_continuous H f

#print continuous

definition id_is_homeomorphism {α : Type u} {X : topological_space α} : homeomorphism X X := {
  to_fun := id,
  inv_fun := id,
  left_inv := 
    begin
      unfold function.left_inverse,
      intro x,
      simp,
    end,
  right_inv :=
    begin
      unfold function.right_inverse,
      intro x,
      simp,
    end,
  to_is_continuous := 
    begin 
      unfold continuous,
      unfold set.preimage,
      intros s H1,
      exact H1, 
    end,
  from_is_continuous := 
    begin 
      unfold continuous,
      unfold set.preimage,
      intros s H1,
      exact H1, 
    end,
}
theorem homeomorphism_is_reflexive : reflexive (λ X Y : Σ α, topological_space α, is_homeomorphic_to X.2 Y.2) :=
begin 
  unfold reflexive,
  intro x,
  unfold is_homeomorphic_to,
  have hom : homeomorphism (x.snd) (x.snd),
    exact id_is_homeomorphism,
  exact ⟨hom⟩, 
end

theorem homeomorphism_is_symmetric : symmetric (λ X Y : Σ α, topological_space α, is_homeomorphic_to X.2 Y.2) :=
begin
  unfold symmetric,
  intros x y Hxy,
  unfold is_homeomorphic_to, unfold is_homeomorphic_to at Hxy,
  have homto : homeomorphism x.snd y.snd,
    exact classical.choice Hxy,
  have homfrom : homeomorphism y.snd x.snd,
    exact {to_fun := homto.inv_fun, inv_fun := homto.to_fun, left_inv := homto.right_inv, right_inv := homto.left_inv, to_is_continuous := homto.from_is_continuous, from_is_continuous := homto.to_is_continuous},
  exact nonempty.intro homfrom,
end

theorem homeomorphism_is_transitive : transitive (λ X Y : Σ α, topological_space α, is_homeomorphic_to X.2 Y.2) :=
begin
  unfold transitive,
  intros x y z Hxy Hyz,
  unfold is_homeomorphic_to at *,
  have homxy : homeomorphism x.snd y.snd, by exact classical.choice Hxy,
  have homyz : homeomorphism y.snd z.snd, by exact classical.choice Hyz,
  have homxz : homeomorphism x.snd z.snd,
    exact {to_fun := homyz.to_fun ∘ homxy.to_fun, 
    inv_fun := homxy.inv_fun ∘ homyz.inv_fun, 
    left_inv := begin 
      unfold function.left_inverse,
      simp,
      intro a,
      have H1 : (homyz.to_equiv).inv_fun ∘ (homyz.to_equiv).to_fun = id,
        exact function.id_of_left_inverse homyz.left_inv,
      rw function.funext_iff at H1,
      simp at H1,
      rw H1,
      have H2 : (homxy.to_equiv).inv_fun ∘ (homxy.to_equiv).to_fun = id,
        exact function.id_of_left_inverse homxy.left_inv,
      rw function.funext_iff at H2,
      simp at H2,
      rw H2,
    end, 
    right_inv := begin
      unfold function.right_inverse,
      unfold function.left_inverse,
      simp,
      intro a,
      have H1: (homxy.to_equiv).to_fun ∘ (homxy.to_equiv).inv_fun = id,
        exact function.id_of_right_inverse homxy.right_inv,
      rw function.funext_iff at H1,
      simp at H1,
      rw H1,
      have H2 : (homyz.to_equiv).to_fun ∘ (homyz.to_equiv).inv_fun = id,
        exact function.id_of_right_inverse homyz.right_inv,
      rw function.funext_iff at H2,
      simp at H2,
      rw H2,
    end, 
    to_is_continuous := begin
      exact @continuous.comp _ _ _ x.2 y.2 z.2 _ _ homxy.to_is_continuous homyz.to_is_continuous,
    end, 
    from_is_continuous := begin
      exact @continuous.comp _ _ _ z.2 y.2 x.2 _ _ homyz.from_is_continuous homxy.from_is_continuous,
    end},
  exact nonempty.intro homxz,
end

theorem homeomorphism_is_equivalence : equivalence (λ X Y : Σ α, topological_space α, is_homeomorphic_to X.2 Y.2) := ⟨homeomorphism_is_reflexive, homeomorphism_is_symmetric, homeomorphism_is_transitive⟩ 

theorem continuous_basis_to_continuous {α : Type*} {β : Type*} [X : topological_space α] [Y : topological_space β] : ∀ f : α → β, (∀ B : set (set β), topological_space.is_topological_basis B → (∀ b : B, is_open (f ⁻¹' b)) → continuous f) :=
begin
  intros f Basis HBasis HBasisInverses U HU,
  have HU_union_basis : ∃ S ⊆ Basis, U = ⋃₀ S, by exact topological_space.sUnion_basis_of_is_open HBasis HU,
  cases HU_union_basis with S HS,
  cases HS with HS1 HS2,
  rw HS2,
  rw set.preimage_sUnion,
  have f_inv_t_open : ∀ t : set β, t ∈ S → topological_space.is_open X (f ⁻¹' t),
    intros t HtS,
    have t_is_open : topological_space.is_open Y t,
      exact topological_space.is_open_of_is_topological_basis HBasis (set.mem_of_subset_of_mem HS1 HtS),
    simp at HBasisInverses,
    exact HBasisInverses t (set.mem_of_subset_of_mem HS1 HtS),
  let set_of_preimages : set (set α) := {x | ∃ t ∈ S, x = f ⁻¹' t},
  have preimages_are_open : topological_space.is_open X (⋃₀ set_of_preimages),
    have H3 : ∀ (t : set α), t ∈ set_of_preimages → topological_space.is_open X t,
      intros tinv Htinv,
      simp at Htinv,
      cases Htinv with t Ht,
      rw Ht.2,
      exact f_inv_t_open t Ht.1,
    exact X.is_open_sUnion set_of_preimages H3,  
  unfold is_open,
  have equal : (⋃₀ set_of_preimages) = (⋃ (t : set β) (H : t ∈ S), f ⁻¹' t),
    rw set.sUnion_eq_Union,
    apply set.ext,
    intro x,
    split,
      intro Hx,
      simp,  
      simp at Hx,
      cases Hx with f_inv_t Hf_inv_t,
      cases Hf_inv_t.1 with t Ht,
      existsi t,
      split,
        exact Ht.1,
      rw ← set.mem_preimage_eq,
      rw ← Ht.2,
      exact Hf_inv_t.2,
    intro Hx,
    simp,
    rw set.mem_Union_eq at Hx,
    cases Hx with i Hi,
    simp at Hi,
    existsi (f ⁻¹' i),
    split,
      existsi i,
      exact ⟨Hi.1, eq.refl (f ⁻¹' i)⟩,
    simp,
    exact Hi.2,
  rw ← equal,
  assumption,
end

