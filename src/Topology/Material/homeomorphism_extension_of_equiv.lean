import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space

import data.equiv.basic


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
