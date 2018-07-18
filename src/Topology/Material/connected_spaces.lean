import analysis.topology.topological_space
import analysis.topology.continuity
import data.set.basic
import logic.basic

open set filter lattice classical
local attribute [instance] prop_decidable

universe u
variables {α : Type u} {β : Type u} {γ : Type u} {δ : Type u}


def is_clopen [t : topological_space α] (s : set α) : Prop := is_open s ∧ is_closed s 

def is_open_in_subspace [t : topological_space α] (A : set α) (V : set α) : Prop := ∃ U, V = A ∩ U ∧ is_open U 

/- For subsets, connected def needs to 
consider open sets in the subspace topology. 
(TODO: unify this with connectedness of univ). -/

def is_connected [t : topological_space α] (s : set α) : Prop := ∀ U' V' : set α, 
is_open_in_subspace s U' ∧ is_open_in_subspace s V' → ¬( (U') ∪ (V') = s ∧ (U') ∩ (V') = ∅ ∧ U' ≠ ∅ ∧ V' ≠ ∅) 

def is_separated [topological_space α] (s t : set α) : Prop := (closure s) ∩ t = ∅ ∧ s ∩ (closure t) = ∅

class connected_space (α : Type u) extends topological_space α :=
    (clopen_trivial : (∀ s : set α, is_clopen s → (s = univ ∨ s = ∅)))

/- This is me cheating and defining a two point discrete space using the bools,
but without any clever coercion since I have no idea how to do this yet. -/

class discrete_two_point_space extends topological_space bool :=
(discreteness : ∀ U : set bool, is_open U)

-----------------------------------------------------------------

theorem open_imp_inter_open_in_subspace [topological_space α] {s t v : set α} :
is_open t → is_open_in_subspace s (t ∩ s) :=
begin
  intro h1,
  show is_open_in_subspace s (t ∩ s), 
    {rw is_open_in_subspace, by exact exists.intro t ⟨inter_comm t s, h1⟩},
end

-----------------------------------------------------------------
-- Some useful set theory lemmas

lemma disjoint_and_union_univ_imp_compl {A B : set α} (hU : A ∪ B = univ) 
(hE : A ∩ B = ∅) : A = -B :=
begin
  have h1 : ∀ x, x ∈ A → x ∈ -B,
    {intros x hA hc, rw eq_empty_iff_forall_not_mem at hE,
    by exact absurd ((mem_inter_iff _ _ _).mpr ⟨hA,hc⟩) (hE x)},
  have h2 : ∀ x, x ∈ -B → x ∈ A,
    {intros x hB, by_contradiction hc,
    have a1 := not_mem_of_mem_compl hB, have a2 := and.intro hc a1, 
    have a3 : x ∈ A ∪ B, {rw [hU], simp}, have a4 := mem_or_mem_of_mem_union a3,
    by exact or.elim a4
        (assume b1, by exact absurd b1 a2.1)
        (assume b2, by exact absurd b2 a2.2)},
  rw [←subset_def] at h1 h2, by exact subset.antisymm h1 h2,
end

lemma eq_compl_iff_compl_eq {A B : set α} : A = -B ↔ B = -A :=
begin
  apply iff.intro, 
    intro H1, by_contradiction HC, rw [H1,compl_compl] at HC, contradiction,
  intro H2, by_contradiction HC, rw [H2,compl_compl] at HC, contradiction,
end

lemma neq_empty_imp_empty_to_union {A B : set α} (H : ¬A = ∅ → B = ∅) :
A = ∅ ∨ B = ∅ :=
begin
  by_contradiction hc, rw [not_or_distrib] at hc, 
  by exact absurd (H hc.1) hc.2,
end



lemma closure_eq_interior_iff_clopen [topological_space α] :
(∀ s : set α, closure s = interior s ↔ is_clopen s) := 
begin
  intro s,
    have A : s ⊆ closure s, from subset_closure,
    have B : interior s ⊆ s, from interior_subset,

  apply iff.intro, assume h1,
    rw is_clopen, apply and.intro,

      have C : interior s = s,
        begin 
          rw [h1] at A, exact subset.antisymm B A,
        end,
    rw [←C], exact is_open_interior,

      have D : closure s = s,
        begin 
          rw [←h1] at B, exact subset.antisymm B A,
        end,
    rw [←D], exact is_closed_closure,

  assume H1, rw is_clopen at H1,
    have Hop, from H1.left,
    have Hcl, from H1.right,
    rw [←closure_eq_iff_is_closed] at Hcl,
    rw [←interior_eq_iff_open] at Hop, rw [Hop, Hcl],
end



theorem empty_frontier_iff_clopen [topological_space α] :
(∀ s : set α, frontier s = ∅ ↔ is_clopen s) :=
begin
  intro h1, 

  apply iff.intro, 
    rw [frontier_eq_closure_inter_closure], 
    intro h2, simp at h2, 

    have hC : ∀ x, x ∈ closure h1 → x ∈ interior h1, 
      begin 
        intros x c1, 
          have c2 : x ∈ closure h1 → x ∉ -interior h1,
            by_contradiction cn, simp at cn, 
              have c3 : x ∈ -interior h1, from cn.right,

              have c4 : x ∈ closure h1 ∩ -interior h1,
                begin
                  have c5, from (and.intro c1 c3), 
                  rw [←mem_inter_iff] at c5, assumption,
                end,

              have c6 : closure h1 ∩ -interior h1 ≠ ∅,
                begin
                  rw [ne_empty_iff_exists_mem], 
                  exact (exists.intro x c4),
                end,

            exact absurd h2 c6,
              have c7 : x ∉ -interior h1, from c2 c1,
            simp at c7, assumption,
      end, 

      rw [←subset_def] at hC,
      have hD : interior h1 ⊆ closure h1, from interior_subset_closure,
      have hE : closure h1 = interior h1, from subset.antisymm hC hD,
      rwa [←closure_eq_interior_iff_clopen], 
    
  intro H1, rw [is_clopen] at H1,   
  have H2 : closure h1 = h1, from closure_eq_iff_is_closed.mpr H1.right,
  have H3 : interior h1 = h1, from interior_eq_iff_open.mpr H1.left,
  rw [frontier, H2, H3, diff_eq], simp,  
end



lemma components_of_separation_clopen [topological_space α] 
{U1 U2 : set α} (hu1 : is_open U1) (hu2 : is_open U2) : (U1 ∪ U2 = univ ∧ U1 ∩ U2 = ∅ ∧ U1 ≠ ∅ ∧ U2 ≠ ∅) → 
is_clopen U1 ∧ is_clopen U2 :=
begin 
  intro H,
  have h2 : U1 = -U2, from
    begin
    rw [set_eq_def], intro y, apply iff.intro,
      by_contradiction hc, simp at hc,
      rw [←mem_inter_iff] at hc,
      apply absurd H.2.1 (ne_empty_iff_exists_mem.mpr (exists.intro y hc)),
    simp, intro hy,
    exact or.elim ((mem_union y U1 U2).mp ((eq_univ_iff_forall.mp H.1) y)) 
      (assume hp : y ∈ U1, by exact hp) 
      (assume hq : y ∈ U2, by exact false.elim (hy hq)),
    end, 
  have h3 : -U1 = U2,
    begin
    rw h2, exact compl_compl U2,
    end,
  have hu1c : is_closed U1,
    begin
    rw [←h3] at hu2, rwa is_closed,
    end,
  have hu2c : is_closed U2, 
    begin
    rw h2 at hu1, rwa is_closed, 
    end,
  exact ⟨⟨hu1,hu1c⟩,⟨hu2,hu2c⟩⟩,  
end 



lemma open_separation_to_closed [topological_space α] 
{U1 U2 : set α} (hu1 : is_open U1) (hu2 : is_open U2) : (U1 ∪ U2 = univ ∧ U1 ∩ U2 = ∅ ∧ U1 ≠ ∅ ∧ U2 ≠ ∅) → 
is_closed U1 ∧ is_closed U2 :=
begin 
  intro H,
  have h2 : U1 = -U2, from
    begin
    rw [set_eq_def], intro y, apply iff.intro,
      by_contradiction hc, simp at hc,
      rw [←mem_inter_iff] at hc,
      apply absurd H.2.1 (ne_empty_iff_exists_mem.mpr (exists.intro y hc)),
    simp, intro hy,
    exact or.elim ((mem_union y U1 U2).mp ((eq_univ_iff_forall.mp H.1) y)) 
      (assume hp : y ∈ U1, by exact hp) 
      (assume hq : y ∈ U2, by exact false.elim (hy hq)),
    end, 
  have h3 : -U1 = U2,
    begin
    rw h2, exact compl_compl U2,
    end,
  have hu1c : is_closed U1,
    begin
    rw [←h3] at hu2, rwa is_closed,
    end,
  have hu2c : is_closed U2, 
    begin
    rw h2 at hu1, rwa is_closed, 
    end,
  exact ⟨hu1c,hu2c⟩,  
end 



lemma closed_separation_to_open [topological_space α] 
{U1 U2 : set α} (hu1 : is_closed U1) (hu2 : is_closed U2) : (U1 ∪ U2 = univ ∧ U1 ∩ U2 = ∅ ∧ U1 ≠ ∅ ∧ U2 ≠ ∅) → 
is_open U1 ∧ is_open U2 :=
begin 
  intro H,
  have h2 : U1 = -U2, from
    begin
    rw [set_eq_def], intro y, apply iff.intro,
      by_contradiction hc, simp at hc,
      rw [←mem_inter_iff] at hc,
      apply absurd H.2.1 (ne_empty_iff_exists_mem.mpr (exists.intro y hc)),
    simp, intro hy,
    exact or.elim ((mem_union y U1 U2).mp ((eq_univ_iff_forall.mp H.1) y)) 
      (assume hp : y ∈ U1, by exact hp) 
      (assume hq : y ∈ U2, by exact false.elim (hy hq)),
    end, 
  have h3 : -U1 = U2,
    begin
    rw h2, exact compl_compl U2,
    end,
  have hu1c : is_open U1,
    begin
    rw [←h3] at hu2, rwa is_closed at hu2, simp at hu2, assumption,
    end,
  have hu2c : is_open U2, 
    begin
    rw h2 at hu1, rwa is_closed at hu1, simp at hu1, assumption, 
    end,
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



------------------------------------------------------------
/- Alternate definitions of connected, proved to be implied by 
the LEAN definition (TODO: Prove complete equivalence). -/


-- 4.
theorem connected_def_empty_frontier_iff_trivial [c : connected_space α] : 
∀ s : set α, frontier s = ∅ ↔ (s = univ ∨ s = ∅) := 
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



-- 1.
theorem connected_def_open_separation [c : connected_space α] : ∀ U V : set α, 
is_open U ∧ is_open V → ¬( U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅ ) := 
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



-- 2.
theorem connected_def_closed_separation [c : connected_space α] : ∀ U V : set α, 
is_closed U ∧ is_closed V → ¬( U ∪ V = univ ∧ U ∩ V = ∅ ∧ U ≠ ∅ ∧ V ≠ ∅ ) :=
begin
  exact no_open_sep_iff_no_closed_sep.mp connected_def_open_separation, 
end



-- 3.
-- clopen_trivial, the chosen definition



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



-- 6. (TODO: use coercion rather than using bool itself?)
theorem connected_def_cts_to_discrete [connected_space α] [discrete_two_point_space] :
∀ f : α → bool, continuous f → ¬function.surjective f :=
begin
  intros f cf, by_contradiction h,
  rw function.surjective at h, rw continuous at cf,

  have hff' : is_open (f ⁻¹' {ff}), 
    from cf {ff} (discrete_two_point_space.discreteness {ff}),
  have htt' : is_open (f ⁻¹' {tt}), 
    from cf {tt} (discrete_two_point_space.discreteness {tt}),

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


------------------------------------------------------------

theorem is_connected_pairwise_union [topological_space α] {A B : set α} :
is_connected A ∧ is_connected B → (A ∩ B ≠ ∅) → is_connected (A ∪ B) := 
begin
  intros hc hn, rw is_connected, intros U' V' huv h,

  have hU'n : U' ≠ ∅, from h.2.2.1, 
  have hV'n : V' ≠ ∅, from h.2.2.2, 
    
  have hUV' : U' ∪ V' = A ∪ B, from h.1,
  
  have d2 : V' ∩ U' = ∅, {have d1, from h.2.1, rwa [inter_comm]},
        
  have hA : A = (A ∩ U') ∪ (A ∩ V'), 
    begin
      have a1 : A ∩ U' ⊆ A, from inter_subset_left _ _ ,  
      have a2 : A ∩ V' ⊆ A, from inter_subset_left _ _ ,
      have a3 : (A ∩ U') ∪ (A ∩ V') ⊆ A, from union_subset a1 a2,
      have a4 : A ⊆ (A ∩ U') ∪ (A ∩ V'), 
        begin 
          rw subset_def, intros x e1,
          suffices t : x ∈ U' ∪ V', 
          from or.elim ((mem_union _ _ _).mp t) 
            (assume h1 : x ∈ U', by exact (mem_union _ _ _).mpr 
            (or.inl ((mem_inter_iff _ _ _).mpr ⟨e1,h1⟩)))
            (assume h2 : x ∈ V', by exact (mem_union _ _ _).mpr 
            (or.inr ((mem_inter_iff _ _ _).mpr ⟨e1,h2⟩))),
          have q1 : x ∈ A ∪ B, exact (mem_union_left B) e1,
          rwa [←h.1] at q1, 
        end,
      exact eq_comm.mp (subset.antisymm a3 a4),
    end, 
  have hB : B = (B ∩ U') ∪ (B ∩ V'), 
    begin
      have a1 : B ∩ U' ⊆ B, from inter_subset_left _ _ ,  
      have a2 : B ∩ V' ⊆ B, from inter_subset_left _ _ ,
      have a3 : (B ∩ U') ∪ (B ∩ V') ⊆ B, from union_subset a1 a2,
      have a4 : B ⊆ (B ∩ U') ∪ (B ∩ V'), 
        begin 
          rw subset_def, intros x e1,
          suffices t : x ∈ U' ∪ V', 
          from or.elim ((mem_union _ _ _).mp t) 
            (assume h1 : x ∈ U', by exact (mem_union _ _ _).mpr 
            (or.inl ((mem_inter_iff _ _ _).mpr ⟨e1,h1⟩)))
            (assume h2 : x ∈ V', by exact (mem_union _ _ _).mpr 
            (or.inr ((mem_inter_iff _ _ _).mpr ⟨e1,h2⟩))),
          have q1 : x ∈ A ∪ B, exact (mem_union_right A) e1,
          rwa [←h.1] at q1, 
        end,
      exact eq_comm.mp (subset.antisymm a3 a4),
    end,  


  have hd : (A ∩ U') ∩ (A ∩ V') = ∅,
    begin
      rw [inter_assoc,inter_comm,inter_assoc], 
      have d1 : A ∩ V' ∩ A = A ∩ V',
        {rw [inter_comm,←inter_assoc], simp},
      rw [d1,inter_comm,inter_assoc,d2], exact inter_empty A,
    end,
  have he : (B ∩ U') ∩ (B ∩ V') = ∅,
    begin
      rw [inter_assoc,inter_comm,inter_assoc], 
      have e1 : B ∩ V' ∩ B = B ∩ V',
        {rw [inter_comm,←inter_assoc], simp},
      rw [e1,inter_comm,inter_assoc,d2], exact inter_empty B,
    end,

  have pA1, from hc.1, rw is_connected at pA1, 
  have pB1, from hc.2, rw is_connected at pB1,
  
  have S1, from huv.1, rw is_open_in_subspace at S1,
  have S2, from huv.2, rw is_open_in_subspace at S2,

  have R2 : ∀ A B C : set α, A ∩ (A ∪ B) ∩ C = A ∩ C,
    begin
      intros A B C, 
      have R3 : ∀ x, x ∈ A ∩ (A ∪ B) ∩ C → x ∈ A ∩ C,
        {intros x Hx, rw [mem_inter_iff] at Hx, have Hy, from Hx.1, 
        rw [mem_inter_iff] at Hy, by exact (mem_inter_iff _ _ _).mpr ⟨Hy.1,Hx.2⟩},
      have R4 : ∀ x, x ∈ A ∩ C → x ∈ A ∩ (A ∪ B) ∩ C,
        {intros x Hx, rw [mem_inter_iff] at Hx, 
        have m1 : x ∈ (A ∪ B), by exact mem_union_left _ Hx.1,
        by exact (mem_inter_iff _ _ _).mpr ⟨ (mem_inter_iff _ _ _).mpr ⟨Hx.1,m1⟩ , Hx.2⟩},
      rw [←subset_def] at R3 R4, by exact subset.antisymm R3 R4,
    end,

  have R5 : ∀ U' A B U : set α, U' = (A ∪ B) ∩ U → A ∩ U' = A ∩ U,
    begin
      intros U' A B U heq, rw [heq,←inter_assoc], by exact R2 A B U,
    end,

  have R6 : ∀ U' A B U : set α, U' = (A ∪ B) ∩ U → B ∩ U' = B ∩ U,
    begin
      intros U' A B U, rw [union_comm], intro heq, rw [heq,←inter_assoc], by exact R2 B A U,
    end,

  have R1 : is_open_in_subspace A (A ∩ U'), 
    begin
      by exact exists.elim S1 
        (assume U, 
          assume hw : U' = (A ∪ B) ∩ U ∧ is_open U,
          show ∃ (U : set α), A ∩ U' = A ∩ U ∧ is_open U,
          from ⟨U, ⟨R5 U' A B U hw.1, hw.2⟩ ⟩) 
    end,

  have Q1 : is_open_in_subspace A (A ∩ V'), 
    begin
      by exact exists.elim S2 
        (assume U, 
          assume hw : V' = (A ∪ B) ∩ U ∧ is_open U,
          show ∃ (U : set α), A ∩ V' = A ∩ U ∧ is_open U,
          from ⟨U, ⟨R5 V' A B U hw.1, hw.2⟩ ⟩) 
    end,

  have T1 : is_open_in_subspace B (B ∩ U'), 
    begin
      by exact exists.elim S1 
        (assume U, 
          assume hw : U' = (A ∪ B) ∩ U ∧ is_open U,
          show ∃ (U : set α), B ∩ U' = B ∩ U ∧ is_open U,
          from ⟨U, ⟨R6 U' A B U hw.1, hw.2⟩ ⟩) 
    end,

  have T2 : is_open_in_subspace B (B ∩ V'), 
    begin
      by exact exists.elim S2 
        (assume U, 
          assume hw : V' = (A ∪ B) ∩ U ∧ is_open U,
          show ∃ (U : set α), B ∩ V' = B ∩ U ∧ is_open U,
          from ⟨U, ⟨R6 V' A B U hw.1, hw.2⟩ ⟩) 
    end,

  have pA2, from pA1 (A ∩ U') (A ∩ V') ⟨R1,Q1⟩, simp at pA2,
  have pB2, from pB1 (B ∩ U') (B ∩ V') ⟨T1,T2⟩, simp at pB2, 

  rw eq_comm at hA hB,

  have wA1 : ¬A ∩ U' = ∅ → A ∩ V' = ∅, from pA2 hA hd,
  have wB1 : ¬B ∩ U' = ∅ → B ∩ V' = ∅, from pB2 hB he,

  rw [inter_comm] at wA1 wB1,

  have v1 : ¬U' ∩ A = ∅ → V' ∩ A = ∅, {intro hv, have hv2, from wA1 hv, rwa [inter_comm]},
  have v2 : ¬U' ∩ B = ∅ → V' ∩ B = ∅, {intro hv, have hv2, from wB1 hv, rwa [inter_comm]}, 

  have HA : (U' ∩ A = ∅) ∨ (V' ∩ A = ∅),
    by_contradiction HC, rw [not_or_distrib] at HC, 
    exact absurd (v1 HC.1) HC.2,
  have HB : (U' ∩ B = ∅) ∨ (V' ∩ B = ∅),
    by_contradiction HC, rw [not_or_distrib] at HC, 
    exact absurd (v2 HC.1) HC.2,

  have H1 : V' ∩ A = ∅ → A ⊆ U',
    begin
      intro w1, 
      have w2 : ∀ x, x ∈ A → x ∈ U', 
        begin
          intros x hx,
          have w3, from mem_union_left B hx,
          rw [←h.1,mem_union _ _ _] at w3,
          have w4, from ((eq_empty_iff_forall_not_mem.mp w1) x),  
          rw [mem_inter_iff _ _ _,not_and_distrib] at w4,
          exact or.elim w3
            (assume m1 : x ∈ U', by exact m1)
            (assume m2 : x ∈ V', by exact or.elim w4
              (assume n1 : x ∉ V', show x ∈ U', by exact false.elim (absurd m2 n1))
              (assume n2 : x ∉ A, show x ∈ U', by exact false.elim (n2 hx))),  
        end, 
      rwa [←subset_def] at w2,
    end, 

  have H2 : U' ∩ A = ∅ → A ⊆ V',
    begin
      intro w1, 
      have w2 : ∀ x, x ∈ A → x ∈ V', 
        begin
          intros x hx,
          have w3, from mem_union_left B hx,
          rw [←h.1,mem_union _ _ _] at w3,
          have w4, from ((eq_empty_iff_forall_not_mem.mp w1) x),  
          rw [mem_inter_iff _ _ _,not_and_distrib] at w4,
          exact or.elim w3
            (assume m2 : x ∈ U', by exact or.elim w4
              (assume n1 : x ∉ U', show x ∈ V', by exact false.elim (absurd m2 n1))
              (assume n2 : x ∉ A, show x ∈ V', by exact false.elim (n2 hx)))
            (assume m1 : x ∈ V', by exact m1),
        end, 
      rwa [←subset_def] at w2,
    end, 

  have H3 : V' ∩ B = ∅ → B ⊆ U',
    begin
      intro w1, 
      have w2 : ∀ x, x ∈ B → x ∈ U', 
        begin
          intros x hx,
          have w3, from mem_union_right A hx,
          rw [←h.1,mem_union _ _ _] at w3,
          have w4, from ((eq_empty_iff_forall_not_mem.mp w1) x),  
          rw [mem_inter_iff _ _ _,not_and_distrib] at w4,
          exact or.elim w3
            (assume m1 : x ∈ U', by exact m1)
            (assume m2 : x ∈ V', by exact or.elim w4
              (assume n1 : x ∉ V', show x ∈ U', by exact false.elim (absurd m2 n1))
              (assume n2 : x ∉ B, show x ∈ U', by exact false.elim (n2 hx))),  
        end, 
      rwa [←subset_def] at w2,
    end, 

  have H4 : U' ∩ B = ∅ → B ⊆ V',
    begin
      intro w1, 
      have w2 : ∀ x, x ∈ B → x ∈ V', 
        begin
          intros x hx,
          have w3, from mem_union_right A hx,
          rw [←h.1,mem_union _ _ _] at w3,
          have w4, from ((eq_empty_iff_forall_not_mem.mp w1) x),  
          rw [mem_inter_iff _ _ _,not_and_distrib] at w4,
          exact or.elim w3
            (assume m2 : x ∈ U', by exact or.elim w4
              (assume n1 : x ∉ U', show x ∈ V', by exact false.elim (absurd m2 n1))
              (assume n2 : x ∉ B, show x ∈ V', by exact false.elim (n2 hx)))
            (assume m1 : x ∈ V', by exact m1),
        end, 
      rwa [←subset_def] at w2,
    end, 

  rw [inter_comm] at d2,

  have zA : A ⊆ U' ∨ A ⊆ V', exact or.elim HA
    (assume z1 : U' ∩ A = ∅, by exact or.inr (H2 z1))
    (assume z2 : V' ∩ A = ∅, by exact or.inl (H1 z2)),
  have zB : B ⊆ U' ∨ B ⊆ V', exact or.elim HB
    (assume z1 : U' ∩ B = ∅, by exact or.inr (H4 z1))
    (assume z2 : V' ∩ B = ∅, by exact or.inl (H3 z2)),

  have G1 : A ⊆ U' → B ⊆ U' → false,
    begin
      intros f g,
      have g1, from union_subset f g, rw [←hUV',union_subset_iff] at g1,
      have g2 : V' = ∅, 
        begin
        by_contradiction C, rw [not_eq_empty_iff_exists] at C,
        exact absurd d2 (ne_empty_iff_exists_mem.mpr 
        (exists.elim C 
          (assume w, assume hw : w ∈ V', 
            show ∃ x, x ∈ U' ∩ V', from ⟨w, (mem_inter_iff _ _ _).mpr 
            ⟨mem_of_subset_of_mem g1.2 hw, hw⟩⟩ ))), 
        end,
      by exact absurd g2 hV'n,
    end,
  have J1 : A ⊆ U' → B ⊆ V',
    begin
      intro j1, by_contradiction j2,
      have j3 : B ⊆ U', by exact or.elim zB
        (assume k1, by exact k1)
        (assume k2, by exact absurd k2 j2), 
      show false, from G1 j1 j3,
    end,

  have G2 : A ⊆ V' → B ⊆ V' → false,
    begin
      intros f g,
      have g1, from union_subset f g, rw [←hUV',union_subset_iff] at g1,
      have g2 : U' = ∅, 
        begin
        by_contradiction C, rw [not_eq_empty_iff_exists] at C,
        exact absurd d2 (ne_empty_iff_exists_mem.mpr 
        (exists.elim C 
          (assume w, assume hw : w ∈ U', 
            show ∃ x, x ∈ U' ∩ V', from ⟨w, (mem_inter_iff _ _ _).mpr 
            ⟨hw, mem_of_subset_of_mem g1.1 hw⟩⟩ ))), 
        end,
      by exact absurd g2 hU'n,
    end,
  have J2 : A ⊆ V' → B ⊆ U',
    begin
      intro j1, by_contradiction j2,
      have j3 : B ⊆ V', by exact or.elim zB
        (assume k1, by exact absurd k1 j2)
        (assume k2, by exact k2), 
      show false, from G2 j1 j3,
    end,

  have L1 : A ⊆ U' → (A ∩ B) ⊆ (U' ∩ V'),
    {intro l1, by exact inter_subset_inter l1 (J1 l1)}, 
    rw [d2,subset_empty_iff] at L1,
  have L2 : A ⊆ V' → (B ∩ A) ⊆ (U' ∩ V'),
    {intro l1, by exact inter_subset_inter (J2 l1) l1 }, 
    rw [inter_comm,d2,subset_empty_iff] at L2,  
  show false, from or.elim zA
      (assume z1, by exact absurd (L1 z1) hn)
      (assume z2, by exact absurd (L2 z2) hn),
end

 ------------------------------------------------------------

















/-

theorem open_imp_preiage [topological_space α] [topological_space β] (f : α → β) (hf : continuous f) 
(U : set β) : is_open U → is_open (f ⁻¹' U) := 
begin
    intro h1, exact ((assume s h, hf s h) U) h1
end

theorem cts_image_of_connected_is_connected [connected_space α] [topological_space β]
{f : α → β} (hf : continuous f) : ∀ s : set α, is_connected s → is_connected (f '' s) :=
begin
intros hs hcs, by_contradiction h, rw is_connected at h, rw [classical.not_forall] at h, simp at h,
end
 



theorem M2PM5_sheet3_question1_4 [topological_space α] [topological_space β] {f : α → β} (hf : continuous f) 
(V : set β) : is_closed V → is_closed (f ⁻¹' V) := 
begin
   intro h1, have hs, from continuous_iff_is_closed.mp hf,
   exact ((assume s h, hs s h) V) h1,
end


-/
