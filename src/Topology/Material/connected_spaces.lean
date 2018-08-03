import analysis.topology.topological_space
import analysis.topology.continuity
import data.set.basic
import data.bool
import logic.basic

open set filter lattice classical
local attribute [instance] prop_decidable

universe u
variables {α : Type u} {β : Type u} {γ : Type u} {δ : Type u}


def is_clopen [t : topological_space α] (s : set α) : Prop := is_open s ∧ is_closed s 

/- For subsets, connected def needs to 
consider open sets in the subspace topology. -/

def is_open_in_subspace [t : topological_space α] (A : set α) (V : set α) : Prop := ∃ U, V = A ∩ U ∧ is_open U 

def is_connected [t : topological_space α] (A : set α) : Prop := ∀ U V : set α, 
is_open_in_subspace A U ∧ is_open_in_subspace A V → ¬( U ∪ V = A ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅) 

def is_separated [topological_space α] (s t : set α) : Prop := (closure s) ∩ t = ∅ ∧ s ∩ (closure t) = ∅

class connected_space (α : Type u) extends topological_space α :=
    (clopen_trivial : (∀ s : set α, is_clopen s → (s = univ ∨ s = ∅)))

class discrete_space α extends topological_space α :=
(discreteness : ∀ U : set α, is_open U)

def X : topological_space bool := by apply_instance

class indiscrete_space α extends topological_space α :=
(indiscreteness : ∀ U : set α, ¬is_open U)

class discrete_connected_space α extends connected_space α :=
(discreteness : ∀ U : set α, is_open U)

class indiscrete_connected_space α extends connected_space α :=
(indiscreteness : ∀ U : set α, ¬is_open U)

-----------------------------------------------------------------
-- Some useful lemmas


lemma eq_compl_iff_compl_eq {A B : set α} : A = -B ↔ B = -A := 
by {apply iff.intro, intro H1, rw [H1,compl_compl], intro H2, rw [H2,compl_compl]}


lemma disjoint_and_union_univ_imp_compl {A B : set α} (hU : A ∪ B = univ) 
(hE : A ∩ B = ∅) : A = -B :=
  set.subset.antisymm 
    (subset_compl_iff_disjoint.2 hE : A ⊆ -B) 
    (compl_subset_iff_union.2 $ set.union_comm A B ▸ hU : -B ⊆ A)


lemma neq_empty_imp_empty_to_union {A B : set α} (H : ¬A = ∅ → B = ∅) :
A = ∅ ∨ B = ∅ :=
begin
  by_contradiction hc, rw [not_or_distrib] at hc, 
  by exact absurd (H hc.1) hc.2,
end


lemma in_right_union_univ {A B : set α} {x : α} (H : A ∪ B = univ) : x ∉ A → x ∈ B :=
begin
  intro hx, 
  by exact or.elim ((mem_union _ _ _).mp (eq_univ_iff_forall.mp H x))
    (assume a1, by exact absurd a1 hx)
    (assume a2, by exact a2),
end


lemma in_left_union_univ {A B : set α} {x : α} (H : A ∪ B = univ) : x ∉ B → x ∈ A :=
begin
  intro hx, 
  by exact or.elim ((mem_union _ _ _).mp (eq_univ_iff_forall.mp H x))
    (assume a2, by exact a2)
    (assume a1, by exact absurd a1 hx),
end


lemma not_in_right_union_empty {A B : set α} {x : α} (H : A ∩ B = ∅) : x ∈ A → x ∉ B :=
by {intros hx hc, exact absurd H (ne_empty_of_mem (mem_inter hx hc))}

lemma not_in_left_union_empty {A B : set α} {x : α} (H : A ∩ B = ∅) : x ∈ B → x ∉ A :=
by {intros hx hc, exact absurd H (ne_empty_of_mem (mem_inter hc hx))}


lemma mem_inter_empty_left {A B : set α} {x : α} (H1 : x ∈ A) (H2 : A ∩ B = ∅) :
x ∉ B := by {by_contradiction HC, exact absurd H2 (ne_empty_of_mem (mem_inter H1 HC))}

lemma mem_inter_empty_right {A B : set α} {x : α} (H1 : x ∈ B) (H2 : A ∩ B = ∅) :
x ∉ A := by {by_contradiction HC, exact absurd H2 (ne_empty_of_mem (mem_inter HC H1))}



lemma eq_union_of_inter_if_subseteq {A B C : set α} (H1 : A ⊆ B ∪ C) : A = (A ∩ B) ∪ (A ∩ C) 
:= by {rw [←inter_distrib_left,inter_eq_self_of_subset_left H1]}

lemma inter_empty_distrib {A B C : set α} (H1 : B ∩ C = ∅) : (A ∩ B) ∩ (A ∩ C) = ∅ 
:= by {rw [inter_left_comm,←inter_assoc,←inter_assoc], simp, rw [inter_assoc,H1], simp}

lemma union_left_inter_distrib {A B C D : set α} : A = (B ∪ C) ∩ D → B ∩ A = B ∩ D
:= by {intro H, rw [H,←inter_assoc, inter_eq_self_of_subset_left (subset_union_left _ _ )]}

lemma union_right_inter_distrib {A B C D : set α} : A = (B ∪ C) ∩ D → C ∩ A = C ∩ D
:= by {intro H, rw [H,←inter_assoc, inter_eq_self_of_subset_left (subset_union_right _ _ )]}

@[simp] lemma inter_union_self_left {A B : set α} : A ∩ (A ∪ B) = A :=
ext (assume x, iff.intro (assume h1, mem_of_mem_inter_left h1) (assume h2, mem_inter h2 (mem_union_left _ h2)))

@[simp] lemma inter_union_self_right {A B : set α} : B ∩ (A ∪ B) = B := 
ext (assume x, iff.intro (assume h1, mem_of_mem_inter_left h1) (assume h2, mem_inter h2 (mem_union_right _ h2)))

-----------------------------------------------------------------

theorem open_imp_inter_open_in_subspace [topological_space α] {s t v : set α} :
is_open t → is_open_in_subspace s (t ∩ s) :=
begin
  intro h1,
  show is_open_in_subspace s (t ∩ s), 
    {rw is_open_in_subspace, by exact exists.intro t ⟨inter_comm t s, h1⟩},
end


lemma sub_union_open_to_open_inter_left [topological_space α] {A B C : set α} 
(H1 : is_open_in_subspace (A ∪ B) C) : is_open_in_subspace A (A ∩ C) :=
by {cases H1 with T HT, exact ⟨T, ⟨union_left_inter_distrib HT.1, HT.2⟩⟩}


lemma sub_union_open_to_open_inter_right [topological_space α] {A B C : set α} 
(H1 : is_open_in_subspace (A ∪ B) C) : is_open_in_subspace B (B ∩ C) :=
by {cases H1 with T HT, exact ⟨T, ⟨union_right_inter_distrib HT.1, HT.2⟩⟩}


lemma closure_subset_imp_eq [topological_space α] {s : set α} 
(H : closure s ⊆ s) : closure s = s := by exact subset.antisymm H subset_closure

lemma subset_interior_imp_eq [topological_space α] {s : set α} 
(H : s ⊆ interior s) : interior s = s := by exact subset.antisymm interior_subset H 


theorem closure_eq_interior_iff_clopen [topological_space α] :
(∀ s : set α, closure s = interior s ↔ is_clopen s) := 
begin
  intro s,
    have A := subset_closure, have B := interior_subset,
  apply iff.intro, assume h1, rw [h1] at A, rw [←h1] at B,
    rw is_clopen, exact ⟨interior_eq_iff_open.mp (subset_interior_imp_eq A),
    closure_eq_iff_is_closed.mp (closure_subset_imp_eq B)⟩, 
  assume H1, rw [closure_eq_iff_is_closed.mpr H1.2, interior_eq_iff_open.mpr H1.1],  
end


theorem empty_frontier_iff_clopen [topological_space α] :
(∀ s : set α, frontier s = ∅ ↔ is_clopen s) :=
begin
  intro s, apply iff.intro, 
    rw [frontier_eq_closure_inter_closure], 
    intro h, simp at h, 
    have h1 : ∀ x, x ∈ closure s → x ∈ interior s, 
      {intros x a1, have a2 := mem_inter_empty_left a1 h, simp at a2, assumption},
    by exact (closure_eq_interior_iff_clopen _ ).mp (subset.antisymm h1 interior_subset_closure),
  intro H1, 
  rw [frontier, closure_eq_iff_is_closed.mpr H1.2, interior_eq_iff_open.mpr H1.1, diff_eq], simp,  
end


lemma components_of_separation_clopen [topological_space α] 
{U1 U2 : set α} (hu1 : is_open U1) (hu2 : is_open U2) : (U1 ∪ U2 = univ ∧ U1 ∩ U2 = ∅ ∧ U1 ≠ ∅ ∧ U2 ≠ ∅) → 
is_clopen U1 ∧ is_clopen U2 :=
begin 
  intro H,
  have h2 : U1 = -U2 := disjoint_and_union_univ_imp_compl H.1 H.2.1, 
  have h3 : -U1 = U2 := eq_comm.mp (eq_compl_iff_compl_eq.mp h2),
  have hu1c : is_closed U1, {rw [←h3] at hu2, rwa is_closed},
  have hu2c : is_closed U2, {rw h2 at hu1, rwa is_closed}, 
  exact ⟨⟨hu1,hu1c⟩,⟨hu2,hu2c⟩⟩,  
end 


lemma components_of_separation_clopen2 [topological_space α] 
{U1 U2 : set α} (hu1 : is_open U1) (hu2 : is_open U2) (hunion : U1 ∪ U2 = univ) 
(hinter : U1 ∩ U2 = ∅) (hnon1 : U1 ≠ ∅) (hnon2 : U2 ≠ ∅) : 
is_clopen U1 ∧ is_clopen U2 :=
begin 
  have h2 : U1 = -U2 := disjoint_and_union_univ_imp_compl hunion hinter, 
  have h3 : -U1 = U2 := eq_comm.mp (eq_compl_iff_compl_eq.mp h2),
  have hu1c : is_closed U1, {rw [←h3] at hu2, rwa is_closed},
  have hu2c : is_closed U2, {rw h2 at hu1, rwa is_closed}, 
  exact ⟨⟨hu1,hu1c⟩,⟨hu2,hu2c⟩⟩,  
end 


lemma open_separation_to_closed [topological_space α] 
{U1 U2 : set α} (hu1 : is_open U1) (hu2 : is_open U2) : (U1 ∪ U2 = univ ∧ U1 ∩ U2 = ∅ ∧ U1 ≠ ∅ ∧ U2 ≠ ∅) → 
is_closed U1 ∧ is_closed U2 :=
begin 
  intro H,
  have h2 : U1 = -U2 := disjoint_and_union_univ_imp_compl H.1 H.2.1, 
  have h3 : -U1 = U2 := eq_comm.mp (eq_compl_iff_compl_eq.mp h2),
  have hu1c : is_closed U1, {rw [←h3] at hu2, rwa is_closed},
  have hu2c : is_closed U2, {rw h2 at hu1, rwa is_closed}, 
  exact ⟨hu1c,hu2c⟩,  
end 


lemma open_separation_to_closed2 [topological_space α] 
  {U1 U2 : set α} (hu1 : is_open U1) (hu2 : is_open U2) (hunion : U1 ∪ U2 = univ)
  (hinter : U1 ∩ U2 = ∅) (hnon1 : U1 ≠ ∅) (hnon2 :U2 ≠ ∅) : is_closed U1 ∧ is_closed U2 :=  
begin 
  have h2 : U1 = -U2 := disjoint_and_union_univ_imp_compl hunion hinter, 
  have h3 : -U1 = U2 := eq_comm.mp (eq_compl_iff_compl_eq.mp h2),
  have hu1c : is_closed U1, {rw [←h3] at hu2, rwa is_closed},
  have hu2c : is_closed U2, {rw h2 at hu1, rwa is_closed}, 
  exact ⟨hu1c,hu2c⟩,  
end 


lemma closed_separation_to_open [topological_space α] 
{U1 U2 : set α} (hu1 : is_closed U1) (hu2 : is_closed U2) : (U1 ∪ U2 = univ ∧ U1 ∩ U2 = ∅ ∧ U1 ≠ ∅ ∧ U2 ≠ ∅) → 
is_open U1 ∧ is_open U2 :=
begin 
  intro H,
  have h2 : U1 = -U2 := disjoint_and_union_univ_imp_compl H.1 H.2.1, 
  have h3 : -U1 = U2 := eq_comm.mp (eq_compl_iff_compl_eq.mp h2),
  have hu1c : is_open U1,
    {rw [←h3] at hu2, rwa is_closed at hu2, simp at hu2, assumption},
  have hu2c : is_open U2, 
    {rw h2 at hu1, rwa is_closed at hu1, simp at hu1, assumption}, 
  exact ⟨hu1c,hu2c⟩,    
end 


lemma closed_separation_to_open2 [topological_space α] 
{U1 U2 : set α} (hu1 : is_closed U1) (hu2 : is_closed U2) (hunion : U1 ∪ U2 = univ)
(hinter : U1 ∩ U2 = ∅) (hnon1 : U1 ≠ ∅) (hnon2 :U2 ≠ ∅) : is_open U1 ∧ is_open U2 :=  
begin 
  have h2 : U1 = -U2 := disjoint_and_union_univ_imp_compl hunion hinter, 
  have h3 : -U1 = U2 := eq_comm.mp (eq_compl_iff_compl_eq.mp h2),
  have hu1c : is_open U1,
    {rw [←h3] at hu2, rwa is_closed at hu2, simp at hu2, assumption},
  have hu2c : is_open U2, 
    {rw h2 at hu1, rwa is_closed at hu1, simp at hu1, assumption}, 
  exact ⟨hu1c,hu2c⟩,  
end 


lemma no_open_sep_iff_no_closed_sep [topological_space α] :
(∀ U1 U2: set α, is_open U1 ∧ is_open U2 → ¬( U1 ∪ U2 = univ ∧ U1 ∩ U2 = ∅ ∧ U1 ≠ ∅ ∧ U2 ≠ ∅))
↔ (∀ V1 V2 : set α, is_closed V1 ∧ is_closed V2 → ¬( V1 ∪ V2 = univ ∧ V1 ∩ V2 = ∅ ∧ V1 ≠ ∅ ∧ V2 ≠ ∅)) :=
begin
  apply iff.intro, 
    intros H1 V1 V2 h1, by_contradiction c1,
    have a1, from closed_separation_to_open h1.1 h1.2 c1, 
    have c2, from H1 V1 V2 a1, 
    apply absurd c1 c2,

  intros H1 U1 U2 h1, by_contradiction c1,
  have a1, from open_separation_to_closed h1.1 h1.2 c1, 
  have c2, from H1 U1 U2 a1, 
  apply absurd c1 c2,
end


lemma closure_union_closure_compl_eq_univ [topological_space α] {A : set α} :
closure A ∪ closure (-A) = univ :=
begin
  have h1 : A ∪ -A = univ := union_compl_self _ ,
  have s1 : A ⊆ closure A := subset_closure,
  have s2 : -A ⊆ closure (-A) := subset_closure,
  have h2 := union_subset_union s1 s2,
  rw h1 at h2, by exact eq_univ_of_univ_subset h2,
end

 
lemma trivial_imp_empty_frontier [topological_space α] (A : set α) :
A = univ ∨ A = ∅ → frontier A = ∅ :=
begin 
  intro g1, rw frontier, 
  by exact or.elim g1
    (assume a1, show closure A \ interior A = ∅, {rw a1, simp, rw [←compl_eq_univ_diff _], simp})
    (assume a1, show closure A \ interior A = ∅, {rw a1, by simp}),
end


------------------------------------------------------------

-- (1) → (2)
lemma one_implies_two [topological_space α] : (∀ U V : set α, is_open U ∧ is_open V → 
¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅)) → (∀ U V : set α, 
is_closed U ∧ is_closed V → ¬( U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅ )) :=
no_open_sep_iff_no_closed_sep.mp

-- (2) → (3) 
lemma two_implies_three [topological_space α] : (∀ U V : set α, is_closed U ∧ is_closed V → 
¬( U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅ )) → (∀ s : set α, frontier s = ∅ ↔ s = univ ∨ s = ∅) :=
begin
  intros h1 s, apply iff.intro, assume h2,
  have h3 : closure s ∩ closure (- s) = ∅, 
    {rwa frontier_eq_closure_inter_closure at h2},
  have h4 : closure s ∪ closure (-s) = univ := closure_union_closure_compl_eq_univ,
  have c1 : is_closed (closure s), by simp,
  have c2 : is_closed (closure (-s)), by simp,
  have h5, from h1 (closure s) (closure (-s)) ⟨c1,c2⟩, simp at h5 h4 h3,
  have h6, from neq_empty_imp_empty_to_union (h5 h4 h3), 
  by exact or.elim h6
    (assume a1, have a2 : s ⊆ ∅, {rw [←a1], by exact subset_closure},
      by exact or.inr (eq_empty_of_subset_empty a2))
    (assume a1, have a2 : -s ⊆ ∅, {rw [←closure_compl_eq] at a1, rw[←a1],
      by exact subset_closure},
      have a3 : -s = ∅ := eq_empty_of_subset_empty a2,
      have a4 : s = univ, {have b1 : -(-s) = -∅, 
      {rw [←a3]}, simp at b1, assumption},
      by exact or.inl a4),

  by exact trivial_imp_empty_frontier s,

end

-- (3) → (4)
lemma three_implies_four [topological_space α] : (∀ s : set α, frontier s = ∅ ↔ s = univ ∨ s = ∅) 
→  (∀ s : set α, is_clopen s → (s = univ ∨ s = ∅)) := 
by {intros H s, rw [←empty_frontier_iff_clopen], by exact (H s).mp}

-- (4) → (5)  
lemma four_implies_five [topological_space α] : (∀ s : set α, is_clopen s → (s = univ ∨ s = ∅)) 
→ (∀ U V : set α, is_separated U V → ¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅)) :=
begin
  intros H U V hsep hc, rw is_separated at hsep,
  have hU := hsep.1,
  have hV := hsep.2,

  have h1 : V = -(closure U),
    {have a1 : closure U ∪ V = univ, 
      {have b1 : U ⊆ closure U ∪ V,
        {have c1 : U ⊆ closure U := subset_closure,
        have c2 : closure U ⊆ closure U ∪ V := subset_union_left (closure U) V,
        by exact subset.trans c1 c2},
      have b2 : U ∪ V ⊆ closure U ∪ V := 
        (union_subset_iff.mpr ⟨b1, subset_union_right (closure U) V⟩),
      rwa [hc.1] at b2,
      by exact eq_univ_of_univ_subset b2},
    {rw [union_comm _ _] at a1, rw [inter_comm _ _] at hU,
     by exact disjoint_and_union_univ_imp_compl a1 hU}},

  have h2 : U = -(closure V),
    {have a1 : U ∪ closure V = univ, 
      {have b1 : V ⊆ U ∪ closure V,
        {have c1 : V ⊆ closure V := subset_closure,
        have c2 : closure V ⊆ U ∪ closure V := subset_union_right U (closure V),
        by exact subset.trans c1 c2},
      have b2 : U ∪ V ⊆ U ∪ closure V := 
        (union_subset_iff.mpr ⟨subset_union_left U (closure V), b1⟩),
      rwa [hc.1] at b2, by exact eq_univ_of_univ_subset b2},
    by exact disjoint_and_union_univ_imp_compl a1 hV},

  have h3 : is_open U, 
    {have a1 : is_closed (closure V) := is_closed_closure, rw h2, rwa is_closed at a1},
  have h4 : is_open V, 
    {have a1 : is_closed (closure U) := is_closed_closure, rw h1, rwa is_closed at a1},
  
  have h5 : U = -V := disjoint_and_union_univ_imp_compl hc.1 hc.2.1,
  have h6 : V = -U := eq_compl_iff_compl_eq.mp h5,

  have h7 : is_closed U, {rwa [is_closed,←h6]},
  have h8 : is_closed V, {rwa [is_closed,←h5]},

  have g1 : is_clopen U := ⟨h3,h7⟩, have g2 : is_clopen V := ⟨h4,h8⟩,

  have g3, from H U g1,
  have g4, from H V g2,

  have UneqV : U ≠ V, 
    {by_contradiction ac, simp at ac, have a1 := hc.2.1,
    rw ac at a1, simp at a1, by exact absurd a1 hc.2.2.2},

  have toUeqV : U = univ → V = univ → U = V, {intros a1 a2, rwa [a2]},

  have g5 : U = univ → false,
    {intro a1, by exact or.elim g4 
      (assume b1, by exact absurd (toUeqV a1 b1) UneqV)
      (assume b2, by exact absurd b2 hc.2.2.2)},

  have g6 : U = ∅ → false, {intro a1, by exact absurd a1 hc.2.2.1},
  
  by exact or.elim g3 (assume a1, by exact g5 a1) (assume a2, by exact g6 a2),

end

-- (5) → (6)
lemma five_implies_six [topological_space α] : (∀ U V : set α, is_separated U V → 
¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅)) → (∀ f : α → bool, continuous f → ¬function.surjective f) :=
begin
  intros H1 f cf, by_contradiction h,
  rw function.surjective at h, rw continuous at cf,

  have h1 : X.is_open {ff}, {unfold X},

  have hff' : is_open (f ⁻¹' {ff}), 
    from cf {ff} (show X.is_open {ff}, {unfold X}),
  have htt' : is_open (f ⁻¹' {tt}), 
    from cf {tt} (show X.is_open {tt}, {unfold X}),

  have hs : (f ⁻¹' {ff}) ∪ (f ⁻¹' {tt}) = @univ α,
    begin
      have a1 : ∀ x, x ∈ (f ⁻¹' {ff}) ∪ (f ⁻¹' {tt}),
        begin
          intro x, rw [mem_union], by_contradiction hx,
          simp at hx, rw [not_or_distrib] at hx, 
          have hy, from hx.1, simp at hx,
          by exact absurd hx.2 hy,
        end,
      rwa [eq_univ_iff_forall],
    end,

  have he : (f ⁻¹' {ff}) ∩ (f ⁻¹' {tt}) = ∅,
    {have a1 : ∀ x, x ∉ (f ⁻¹' {ff}) ∩ (f ⁻¹' {tt}), 
    by simp, by exact eq_empty_iff_forall_not_mem.mpr a1},
       
  have hc1 : (f ⁻¹' {ff}) = -(f ⁻¹' {tt}),
    {by exact disjoint_and_union_univ_imp_compl hs he},

  have hc2 : (f ⁻¹' {tt}) = -(f ⁻¹' {ff}),
    {by exact eq_compl_iff_compl_eq.mp hc1},
   
  
  have Hc1 : closure (f ⁻¹' {ff}) = (f ⁻¹' {ff}),
    {have hclff : is_closed (f ⁻¹' {ff}), {rwa [is_closed,←hc2]}, 
    by exact closure_eq_of_is_closed hclff},
  have Hc2 : closure (f ⁻¹' {tt}) = (f ⁻¹' {tt}),
    {have hcltt : is_closed (f ⁻¹' {tt}), {rwa [is_closed,←hc1]}, 
    by exact closure_eq_of_is_closed hcltt},

  have Hs : is_separated (f ⁻¹' {ff}) (f ⁻¹' {tt}),
    {rw is_separated,
    have a1 : closure (f ⁻¹' {ff}) ∩ (f ⁻¹' {tt}) = ∅, {rwa [Hc1]}, 
    have a2 : f ⁻¹' {ff} ∩ closure (f ⁻¹' {tt}) = ∅, {rwa [Hc2]},
    by exact ⟨a1,a2⟩},

  have HS := H1 (f ⁻¹' {ff}) (f ⁻¹' {tt}) Hs,
  simp at HS, have HS2 := neq_empty_imp_empty_to_union (HS hs he),



  have P : ∀ b : bool, f ⁻¹' {b} = ∅ → false,
    {intros b a1, 
    have a2, from h b, 
    have a3 : ∀ a, f a = b → a ∈ f ⁻¹' {b},
      {intros a b1, rw [mem_preimage_eq,b1], simp},
    have a4 : ∃ x, x ∈ f ⁻¹' {b}, from exists.elim a2 
      (assume x, assume hx : f x = b,
        have hy : x ∈ f ⁻¹' {b} := a3 x hx,
        by exact ⟨x,hy⟩), 
    by exact absurd a1 (ne_empty_iff_exists_mem.mpr a4)},

  by exact or.elim HS2
    (assume a1, by exact P ff a1)
    (assume a2, by exact P tt a2),
end

-- (6) → (1) 
def char_map (A : set α) (x : α) : Prop := x ∈ A

noncomputable def char_map_to_bool (A : set α) (x : α) : bool := to_bool (char_map A x) 

lemma six_implies_one [topological_space α] : (∀ f : α → bool, 
continuous f → ¬function.surjective f) → (∀ U V : set α, is_open U ∧ is_open V → 
¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅)) := 
begin
  intros H1 U V H2 HC,
  have hcompl : U = -V := disjoint_and_union_univ_imp_compl HC.1 HC.2.1,
  have h1 : (char_map_to_bool V) ⁻¹' ∅ = ∅ := rfl,
  have h2 : (char_map_to_bool V) ⁻¹' univ = univ := rfl,

  have h3 : (char_map_to_bool V) ⁻¹' {ff} = U, 
    {have a1 : ∀ x ∈ U, x ∈ (char_map_to_bool V) ⁻¹' {ff},
      {simp, intros x hx, have b1 : x ∉ V, {rwa hcompl at hx},
      rw [char_map_to_bool,char_map], simp, assumption}, 
    have a2 : ∀ x ∈ (char_map_to_bool V) ⁻¹' {ff}, x ∈ U, 
      {simp, intros x hx, rw char_map_to_bool at hx, simp at hx, 
      rw char_map at hx, by exact in_left_union_univ HC.1 hx},
    rw [←subset_def] at a1 a2, by exact subset.antisymm a2 a1},

  have h4 : (char_map_to_bool V) ⁻¹' {tt} = V, 
    {have a1 : ∀ x ∈ V, x ∈ (char_map_to_bool V) ⁻¹' {tt},
      {simp, intros x hx,
      rw [char_map_to_bool,char_map], simp, assumption},
    have a2 : ∀ x ∈ (char_map_to_bool V) ⁻¹' {tt}, x ∈ V,    
      {simp, intros x hx, rw char_map_to_bool at hx, 
      simp at hx, rwa char_map at hx},
    rw [←subset_def] at a1 a2, by exact subset.antisymm a2 a1}, 

  have g1 : is_open (char_map_to_bool V ⁻¹' ∅), {rw h1, simp},
  have g2 : is_open (char_map_to_bool V ⁻¹' univ), {rw h2, simp},
  have g3 : is_open (char_map_to_bool V ⁻¹' {ff}), {rw h3, exact H2.1},
  have g4 : is_open (char_map_to_bool V ⁻¹' {tt}), {rw h4, exact H2.2},

  suffices c1 : continuous (char_map_to_bool V),
    have j1 := H1 (char_map_to_bool V) c1, 
    rw [function.surjective, not_forall] at j1, simp at j1,

    by exact exists.elim j1 
      (assume b a1, 
      have a2 : b = ff ∨ b = tt := bool.dichotomy b,
      by exact or.elim a2 
        (assume bf : b = ff, 
          have c1 : ∀ (x : α), ¬char_map_to_bool V x = ff, {rwa bf at a1},
          have c2 : ∀ (x : α), ¬ x ∈ (char_map_to_bool V ⁻¹' {ff}), {simp, simp at c1, assumption},
          have c3 : ∀ (x : α), ¬ x ∈ U, {rwa h3 at c2},
          have c4 : U = ∅ := eq_empty_iff_forall_not_mem.mpr c3,
          by exact absurd c4 HC.2.2.1)
        (assume bt : b = tt, 
          have c1 : ∀ (x : α), ¬char_map_to_bool V x = tt, {rwa bt at a1},
          have c2 : ∀ (x : α), ¬ x ∈ (char_map_to_bool V ⁻¹' {tt}), {simp, simp at c1, assumption},
          have c3 : ∀ (x : α), ¬ x ∈ V, {rwa h4 at c2},
          have c4 : V = ∅ := eq_empty_iff_forall_not_mem.mpr c3,
          by exact absurd c4 HC.2.2.2)),

  rw continuous,
  have A1 : {ff} ∪ {tt} = @univ bool, 
    {rw eq_univ_iff_forall, intro b, simp, exact bool.dichotomy b},
  have A2 : ∀ y : bool, y ∉ {ff} → y ∈ {tt}, {intro y, exact in_right_union_univ A1},
  have A3 : ∀ y : bool, y ∉ {tt} → y ∈ {ff}, {intro y, exact in_left_union_univ A1},

  have k1 : ∀ s : set bool, s = ∅ ∨ s = univ ∨ s = {ff} ∨ s = {tt},
    begin
      intro s, by_contradiction hc, repeat {rw not_or_distrib at hc},
      have a1 : ∃ b1 : bool, b1 ∈ s := not_eq_empty_iff_exists.mp hc.1,
      have a2 : ∃ b2 : bool, b2 ∉ s, {by_contradiction bc,
        simp at bc, rw [←eq_univ_iff_forall] at bc, exact absurd bc hc.2.1},

      have a3 : ff ∈ s → tt ∈ s,
        {intros c1, have c2 := hc.2.2.1, 
        have hy : ∃ y, y ∈ s ∧ y ≠ ff, by_contradiction cy, simp at cy,
          have hf : s = {ff}, 
            {have hy1 : ∀ y : bool, y ∈ s → y ∈ {ff},
              {intros y d1, 
                have d2 : y ∈ {ff} ∨ y ∈ {tt}, 
                  {rw [←mem_union _ _ _,A1], simp},
                by exact or.elim d2 (assume e1, by exact e1) 
                (assume e2, show y ∈ {ff}, {simp at e2, rw e2 at d1, exact absurd d1 cy})},
            have hy2 : ∀ y : bool, y ∈ {ff} → y ∈ s, {simp, assumption},
            by exact subset.antisymm hy1 hy2},
          by exact absurd hf c2,
        by exact exists.elim hy
          (assume y d1, 
          have d2 : y ∉ {ff} → y ∈ {tt} := A2 y,
          have d3 : y ≠ ff → y = tt, {rwa [mem_singleton_iff,mem_singleton_iff] at d2},
          have d4 : y = tt := d3 d1.2, 
          have d5 : y ∈ s := d1.1, 
          show tt ∈ s, {rwa d4 at d5})},

      have a4 : tt ∈ s → ff ∈ s,
        {intros c1, have c2 := hc.2.2.2, 
        have hy : ∃ y, y ∈ s ∧ y ≠ tt, by_contradiction cy, simp at cy,
          have hf : s = {tt}, 
            {have hy1 : ∀ y : bool, y ∈ s → y ∈ {tt},
              {intros y d1, 
                have d2 : y ∈ {tt} ∨ y ∈ {ff}, 
                  {rw [or_comm,←mem_union _ _ _,A1], simp},
                by exact or.elim d2 (assume e1, by exact e1) 
                (assume e2, show y ∈ {tt}, {simp at e2, rw e2 at d1, exact absurd d1 cy})},
            have hy2 : ∀ y : bool, y ∈ {tt} → y ∈ s, {simp, assumption},
            by exact subset.antisymm hy1 hy2},
          by exact absurd hf c2,
        by exact exists.elim hy
          (assume y d1, 
          have d2 : y ∉ {tt} → y ∈ {ff} := A3 y,
          have d3 : y ≠ tt → y = ff, {rwa [mem_singleton_iff,mem_singleton_iff] at d2},
          have d4 : y = ff := d3 d1.2, 
          have d5 : y ∈ s := d1.1, 
          show ff ∈ s, {rwa d4 at d5})},

      have hX : ∀ b : bool, b = ff ∨ b = tt, {intro b, exact (bool.dichotomy b)},

      have a5 : ff ∈ s,
        {by exact exists.elim a1 
          (assume b : bool, assume Hb : b ∈ s, 
          by exact or.elim (hX b) 
            (assume s1, show ff ∈ s, by {rwa s1 at Hb})
            (assume s1, show ff ∈ s, {rw s1 at Hb, by exact a4 Hb}))},

      have a6 : tt ∈ s,
        {by exact exists.elim a1 
          (assume b : bool, assume Hb : b ∈ s, 
          by exact or.elim ( (or_comm _ _).mp (hX b)) 
            (assume s1, show tt ∈ s, by {rwa s1 at Hb})
            (assume s1, show tt ∈ s, {rw s1 at Hb, by exact a3 Hb}))},
      
      have a7 : ∀ b : bool, b ∈ s,
        {intro b, by exact or.elim (hX b)
          (assume k1, by {rwa [←k1] at a5})
          (assume k2, by {rwa [←k2] at a6})},

      rw [←eq_univ_iff_forall] at a7, by exact absurd a7 hc.2.1,

    end,

  intros s Hs, 

  have B1 : s = ∅ → is_open (char_map_to_bool V ⁻¹' s), {intro h, rwa h},
  have B2 : s = univ → is_open (char_map_to_bool V ⁻¹' s), {intro h, rwa h},
  have B3 : s = {ff} → is_open (char_map_to_bool V ⁻¹' s), {intro h, rwa h},
  have B4 : s = {tt} → is_open (char_map_to_bool V ⁻¹' s), {intro h, rwa h},

  by exact or.elim (k1 s)
    (assume b1 : s = ∅, by exact B1 b1)
    (assume b2 : s = univ ∨ s = {ff} ∨ s = {tt}, 
      by exact or.elim b2
        (assume c1 : s = univ, by exact B2 c1)
        (assume c2 : s = {ff} ∨ s = {tt}, 
          by exact or.elim c2
            (assume d1 : s = {ff}, by exact B3 d1)
            (assume d2 : s = {tt}, by exact B4 d2))),
end


------------------------------------------------------------
/- Alternate definitions of connected, proved to be 
equivalent to the chosen clopen_trivial definition. -/


-- 4.
theorem connected_def_empty_frontier_iff_trivial [c : connected_space α] : 
∀ s : set α, frontier s = ∅ ↔ s = univ ∨ s = ∅ := 
begin
  intro s, apply iff.intro, 
  assume h1,
    have A : is_clopen s, from (empty_frontier_iff_clopen s).mp h1,
    exact connected_space.clopen_trivial _ A, 
  assume h2, 
    have B : is_clopen s, 

    have G : s = univ → is_clopen s,
      assume B1 : s = univ, rw B1, exact ⟨is_open_univ,is_closed_univ⟩,
    have H : s = ∅ → is_clopen s,
      assume B1 : s = ∅, rw B1, exact ⟨is_open_empty,is_closed_empty⟩,
    exact or.elim h2 G H,
  rwa [empty_frontier_iff_clopen],  
end

theorem empty_frontier_iff_trivial_to_connected [topological_space α]
(hs : ∀ s : set α, frontier s = ∅ ↔ s = univ ∨ s = ∅) : connected_space α :=
begin
  have h1 : ∀ s : set α, is_clopen s → s = univ ∨ s = ∅,
    {assume s, by exact (iff.trans (iff.symm (empty_frontier_iff_clopen s)) (hs s)).mp},
    by exact connected_space.mk h1,
end



-- 1.
theorem connected_def_no_open_separation [c : connected_space α] : ∀ U V : set α, 
is_open U ∧ is_open V → ¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅) := 
begin
  intros U V H,
  by_contradiction h, 
  have A, from components_of_separation_clopen H.1 H.2 h,
  have A1, from A.1, have A2, from A.2,
  rw [←empty_frontier_iff_clopen] at A1 A2, 
  rw [connected_def_empty_frontier_iff_trivial] at A1 A2,
  have h2, from h.2.1, 
  have H1 : U = univ → false,
    begin
      assume B1, 
      rw [B1, univ_inter] at h2, 
      apply absurd h2 h.2.2.2,
    end,
   exact or.elim A1 H1 (assume B2 : U = ∅, absurd B2 h.2.2.1),
end

theorem connected_def_no_open_separation2 [c : connected_space α] (U V : set α) 
(hU : is_open U) (hV : is_open V) (hunion : U ∪ V = univ) (hinter : U ∩ V = ∅)
: (U = ∅ ∨ V = ∅) := 
begin
  by_contradiction h, 
  have A, from components_of_separation_clopen2 hU hV hunion hinter (not_or_distrib.mp h).1 (not_or_distrib.mp h).2,
  have H1 : U = univ → false,
    {assume B, rw [B, univ_inter] at hinter, apply absurd hinter (not_or_distrib.mp h).2},
  exact or.elim ((connected_def_empty_frontier_iff_trivial _ ).mp ((empty_frontier_iff_clopen _ ).mpr A.1))
    H1 (assume B : U = ∅, absurd B (not_or_distrib.mp h).1),
end

theorem no_open_separation_to_connected [topological_space α] (H : ∀ U V : set α, 
is_open U ∧ is_open V → ¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅)) : connected_space α :=
begin
  by exact empty_frontier_iff_trivial_to_connected (two_implies_three (one_implies_two H)),
end



-- 2.
theorem connected_def_no_closed_separation [c : connected_space α] : ∀ U V : set α, 
is_closed U ∧ is_closed V → ¬( U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅ ) :=
begin
  exact no_open_sep_iff_no_closed_sep.mp connected_def_no_open_separation, 
end

theorem no_closed_separation_to_connected [topological_space α] (H : ∀ U V : set α, 
is_closed U ∧ is_closed V → ¬( U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅ )) :
connected_space α :=
begin
  by exact empty_frontier_iff_trivial_to_connected (two_implies_three H),
end



-- 3. clopen_trivial, chosen to be the definition of connected



-- 5.
theorem connected_def_separated_sets [c : connected_space α] : ∀ U V : set α,
is_separated U V → ¬( U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅ ) :=
begin
  intros U V hsep hc, rw is_separated at hsep,
  have hU := hsep.1,
  have hV := hsep.2,

  have h1 : V = -(closure U),
    {have a1 : closure U ∪ V = univ, 
      {have b1 : U ⊆ closure U ∪ V,
        {have c1 : U ⊆ closure U := subset_closure,
        have c2 : closure U ⊆ closure U ∪ V := subset_union_left (closure U) V,
        by exact subset.trans c1 c2},
      have b2 : U ∪ V ⊆ closure U ∪ V := 
        (union_subset_iff.mpr ⟨b1, subset_union_right (closure U) V⟩),
      rwa [hc.1] at b2,
      by exact eq_univ_of_univ_subset b2},
    {rw [union_comm _ _] at a1, rw [inter_comm _ _] at hU,
     by exact disjoint_and_union_univ_imp_compl a1 hU}},

  have h2 : U = -(closure V),
    {have a1 : U ∪ closure V = univ, 
      {have b1 : V ⊆ U ∪ closure V,
        {have c1 : V ⊆ closure V := subset_closure,
        have c2 : closure V ⊆ U ∪ closure V := subset_union_right U (closure V),
        by exact subset.trans c1 c2},
      have b2 : U ∪ V ⊆ U ∪ closure V := 
        (union_subset_iff.mpr ⟨subset_union_left U (closure V), b1⟩),
      rwa [hc.1] at b2, by exact eq_univ_of_univ_subset b2},
    by exact disjoint_and_union_univ_imp_compl a1 hV},

  have h3 : is_open U, 
    {have a1 : is_closed (closure V) := is_closed_closure, rw h2, rwa is_closed at a1},
  have h4 : is_open V, 
    {have a1 : is_closed (closure U) := is_closed_closure, rw h1, rwa is_closed at a1},
  
  have h5 : U = -V := disjoint_and_union_univ_imp_compl hc.1 hc.2.1,
  have h6 : V = -U := eq_compl_iff_compl_eq.mp h5,

  have h7 : is_closed U, {rwa [is_closed,←h6]},
  have h8 : is_closed V, {rwa [is_closed,←h5]},

  have g1 : is_clopen U := ⟨h3,h7⟩, have g2 : is_clopen V := ⟨h4,h8⟩,

  have g3, from connected_space.clopen_trivial U g1,
  have g4, from connected_space.clopen_trivial V g2,

  have UneqV : U ≠ V, 
    {by_contradiction ac, simp at ac, have a1 := hc.2.1,
    rw ac at a1, simp at a1, by exact absurd a1 hc.2.2.2},

  have toUeqV : U = univ → V = univ → U = V, {intros a1 a2, rwa [a2]},

  have g5 : U = univ → false,
    {intro a1, by exact or.elim g4 
      (assume b1, by exact absurd (toUeqV a1 b1) UneqV)
      (assume b2, by exact absurd b2 hc.2.2.2)},

  have g6 : U = ∅ → false, {intro a1, by exact absurd a1 hc.2.2.1},
  
  by exact or.elim g3 (assume a1, by exact g5 a1) (assume a2, by exact g6 a2),

end

theorem separated_sets_to_connected [topological_space α]
(H : ∀ U V : set α, is_separated U V → ¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅)) : 
connected_space α :=
begin
  by exact empty_frontier_iff_trivial_to_connected 
  (two_implies_three (one_implies_two (six_implies_one (five_implies_six H)))),
end




-- 6. 
theorem connected_def_cts_to_discrete [connected_space α] :
∀ f : α → bool, continuous f → ¬function.surjective f :=
begin
  intros f cf, by_contradiction h,
  rw function.surjective at h, rw continuous at cf,

  have s1 : X.is_open {ff}, {unfold X},

  have hff' : is_open (f ⁻¹' {ff}), 
    from cf {ff} (show X.is_open {ff}, {unfold X}),
  have htt' : is_open (f ⁻¹' {tt}), 
    from cf {tt} (show X.is_open {tt}, {unfold X}),

  have hs : (f ⁻¹' {ff}) ∪ (f ⁻¹' {tt}) = @univ α,
    begin
      have a1 : ∀ x, x ∈ (f ⁻¹' {ff}) ∪ (f ⁻¹' {tt}),
        begin
          intro x, rw [mem_union], by_contradiction hx,
          simp at hx, rw [not_or_distrib] at hx, 
          have hy, from hx.1, simp at hx,
          by exact absurd hx.2 hy,
        end,
      rwa [eq_univ_iff_forall],
    end,

  have he : (f ⁻¹' {ff}) ∩ (f ⁻¹' {tt}) = ∅,
    {have a1 : ∀ x, x ∉ (f ⁻¹' {ff}) ∩ (f ⁻¹' {tt}), 
    by simp, by exact eq_empty_iff_forall_not_mem.mpr a1},
       
  have hc1 : (f ⁻¹' {ff}) = -(f ⁻¹' {tt}),
    {by exact disjoint_and_union_univ_imp_compl hs he},

  have hc2 : (f ⁻¹' {tt}) = -(f ⁻¹' {ff}),
    {by exact eq_compl_iff_compl_eq.mp hc1},
   
  
  have Hc1 : closure (f ⁻¹' {ff}) = (f ⁻¹' {ff}),
    {have hclff : is_closed (f ⁻¹' {ff}), {rwa [is_closed,←hc2]}, 
    by exact closure_eq_of_is_closed hclff},
  have Hc2 : closure (f ⁻¹' {tt}) = (f ⁻¹' {tt}),
    {have hcltt : is_closed (f ⁻¹' {tt}), {rwa [is_closed,←hc1]}, 
    by exact closure_eq_of_is_closed hcltt},

  have Hs : is_separated (f ⁻¹' {ff}) (f ⁻¹' {tt}),
    {rw is_separated,
    have a1 : closure (f ⁻¹' {ff}) ∩ (f ⁻¹' {tt}) = ∅, {rwa [Hc1]}, 
    have a2 : f ⁻¹' {ff} ∩ closure (f ⁻¹' {tt}) = ∅, {rwa [Hc2]},
    by exact ⟨a1,a2⟩},

  have HS := connected_def_separated_sets (f ⁻¹' {ff}) (f ⁻¹' {tt}) Hs,
  simp at HS, have HS2 := neq_empty_imp_empty_to_union (HS hs he),

  have P : ∀ b : bool, f ⁻¹' {b} = ∅ → false,
    {intros b a1, 
    have a2, from h b, 
    have a3 : ∀ a, f a = b → a ∈ f ⁻¹' {b},
      {intros a b1, rw [mem_preimage_eq,b1], simp},
    have a4 : ∃ x, x ∈ f ⁻¹' {b}, from exists.elim a2 
      (assume x, assume hx : f x = b,
        have hy : x ∈ f ⁻¹' {b} := a3 x hx,
        by exact ⟨x,hy⟩), 
    by exact absurd a1 (ne_empty_iff_exists_mem.mpr a4)},

  by exact or.elim HS2
    (assume a1, by exact P ff a1)
    (assume a2, by exact P tt a2),
end

theorem cts_to_discrete_to_connected [topological_space α] 
(H : ∀ f : α → bool, continuous f → ¬function.surjective f) : connected_space α :=
begin
  by exact empty_frontier_iff_trivial_to_connected 
  (two_implies_three (one_implies_two (six_implies_one H))),
end




------------------------------------------------------------


lemma subset_inter_empty_right {A B C : set α} (H1 : A ⊆ B ∪ C) (H2 : A ∩ B = ∅) :
A ⊆ C := 
begin
  rw [subset_def] at H1, rw subset_def, intros x hx,
  by exact or.elim (mem_or_mem_of_mem_union (H1 x hx))
    (assume a1, by exact absurd a1 (not_in_right_union_empty H2 hx)) (by simp)
end 

lemma subset_inter_empty_left {A B C : set α} (H1 : A ⊆ B ∪ C) (H2 : A ∩ C = ∅) :
A ⊆ B := 
begin
  rw [subset_def] at H1, rw subset_def, intros x hx,
  by exact or.elim (mem_or_mem_of_mem_union (H1 x hx))
    (by simp) (assume a1, by exact absurd a1 (not_in_right_union_empty H2 hx))
end 

lemma subsets_of_disjoint {A B C D : set α} (H1 : A ⊆ C) (H2 : B ⊆ D) (H3 : C ∩ D = ∅) :
A ∩ B = ∅ := 
by {have H4 := inter_subset_inter H1 H2, rw [H3] at H4, exact eq_empty_of_subset_empty H4}

lemma inter_union_empty_eq_union_empty_left {A B C D : set α} (H1 : A ∩ (C ∪ D) = ∅) (H2 : A ∪ B = C ∪ D) :
A = ∅ := by {rw [←H2] at H1, simp at H1, assumption}

lemma inter_union_empty_eq_union_empty_right {A B C D : set α} (H1 : B ∩ (C ∪ D) = ∅) (H2 : A ∪ B = C ∪ D) :
B = ∅ := by {rw [←H2] at H1, simp at H1, assumption}

lemma inter_union_lemma_1 {A B C : set α} (H1 : A ∩ B = ∅) (H2 : A ∩ C = ∅) :
A ∩ (B ∪ C) = ∅ := by {rw [inter_distrib_left,H1,H2], simp}

lemma inter_eq_comm {A B C : set α} (H1 : A ∩ B = C) : B ∩ A = C := by {rwa inter_comm}


theorem is_connected_pairwise_union [topological_space α] {A B : set α} :
is_connected A ∧ is_connected B → (A ∩ B ≠ ∅) → is_connected (A ∪ B) := 
begin
  intros hc hn, rw is_connected, intros U' V' huv h,  

  have T1 : A ⊆ U' ∪ V', {rw h.1, simp},
  have T2 : B ⊆ U' ∪ V', {rw h.1, simp},

  have hA := eq_union_of_inter_if_subseteq T1,
  have hB := eq_union_of_inter_if_subseteq T2,

  have pA2, from hc.1 (A ∩ U') (A ∩ V') 
    ⟨sub_union_open_to_open_inter_left huv.1,sub_union_open_to_open_inter_left huv.2⟩, 
  have pB2, from hc.2 (B ∩ U') (B ∩ V') 
    ⟨sub_union_open_to_open_inter_right huv.1,sub_union_open_to_open_inter_right huv.2⟩, 

  simp at pA2, simp at pB2, rw eq_comm at hA hB,

  have wA1 : ¬A ∩ U' = ∅ → A ∩ V' = ∅, from pA2 hA (inter_empty_distrib h.2.1),
  have wB1 : ¬B ∩ U' = ∅ → B ∩ V' = ∅, from pB2 hB (inter_empty_distrib h.2.1),
  rw [inter_comm] at wA1 wB1,
  have v1 : ¬U' ∩ A = ∅ → V' ∩ A = ∅, {intro hv, have hv2, from wA1 hv, rwa [inter_comm]},
  have v2 : ¬U' ∩ B = ∅ → V' ∩ B = ∅, {intro hv, have hv2, from wB1 hv, rwa [inter_comm]}, 

  have zA : A ⊆ U' ∨ A ⊆ V', exact or.elim (neq_empty_imp_empty_to_union v1)
    (assume z1, by {rw inter_comm at z1, exact or.inr (subset_inter_empty_right T1 z1)})
    (assume z2, by {rw inter_comm at z2, exact or.inl (subset_inter_empty_left T1 z2)}),

  have zB : B ⊆ U' ∨ B ⊆ V', exact or.elim (neq_empty_imp_empty_to_union v2)
    (assume z1, by {rw inter_comm at z1, exact or.inr (subset_inter_empty_right T2 z1)})
    (assume z2, by {rw inter_comm at z2, exact or.inl (subset_inter_empty_left T2 z2)}),

  have H1 := neq_empty_imp_empty_to_union v1,
  have H2 := neq_empty_imp_empty_to_union v2,

  cases H1 with P1 P2,
    cases H2 with P3 P4,
      exact absurd (inter_union_empty_eq_union_empty_left (inter_union_lemma_1 P1 P3) h.1) h.2.2.1,
      exact absurd (inter_eq_comm (subsets_of_disjoint (subset_inter_empty_left T2 (inter_eq_comm P4))
      (subset_inter_empty_right T1 (inter_eq_comm P1)) h.2.1)) hn,
    cases H2 with P5 P6,
      exact absurd (subsets_of_disjoint (subset_inter_empty_left T1 (inter_eq_comm P2))
      (subset_inter_empty_right T2 (inter_eq_comm P5)) h.2.1) hn,
      exact absurd (inter_union_empty_eq_union_empty_right (inter_union_lemma_1 P2 P6) h.1) h.2.2.2,
end



theorem open_in_univ_iff_open [topological_space α] {U : set α} :
is_open U ↔ is_open_in_subspace univ U :=
begin
  apply iff.intro, 
    intro H, rw is_open_in_subspace,
    have h1 : U = univ ∩ U, {simp},
    by exact exists.intro U ⟨h1,H⟩,
  intro H, rw is_open_in_subspace at H,  
  by exact exists.elim H 
  (assume V, assume hV, show is_open U, 
  {have b1, from is_open_inter is_open_univ hV.2, rwa [hV.1]}),
end


theorem connected_if_univ_connected [topological_space α] :
is_connected (@univ α) → connected_space α :=
begin
  rw is_connected, intros H, 
  have h1 : ∀ U V : set α, is_open U ∧ is_open V → ¬(U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅),  
    {intros U V, repeat {rw [open_in_univ_iff_open]}, by exact H U V},
  by exact no_open_separation_to_connected h1,
end



theorem is_connected_univ [connected_space α] : is_connected (@univ α) :=
begin
  rw is_connected, intros U V h1, repeat {rw [←open_in_univ_iff_open] at h1},
  by exact connected_def_no_open_separation U V h1,
end



theorem is_connected_empty [connected_space α] : is_connected (∅ : set α) :=
begin
  rw is_connected, intros U V h1 hc, repeat {rw is_open_in_subspace at h1},
  have h2 : ∀ V : set α, ∅ ∩ V = ∅, {intro V, by exact empty_inter V},
  show false, from exists.elim h1.1 (assume U1, assume hU1, have a1 : U = ∅,
    {rw [h2 U1] at hU1, by exact hU1.1}, by exact absurd a1 hc.2.2.1),
end



 ------------------------------------------------------------

