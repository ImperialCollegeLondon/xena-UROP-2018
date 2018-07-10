import analysis.topology.topological_space
import analysis.topology.continuity
import data.set.basic

--- Moved from UROP - private (Luca)


open set filter lattice classical
local attribute [instance] prop_decidable

universe u
variables {α : Type u} {β : Type u} {γ : Type u} {δ : Type u}


section

variables [t : topological_space α]
include t

def is_clopen (s : set α) : Prop := is_open s ∧ is_closed s 

def is_separated (s t : set α) : Prop := -s ∩ t = ∅ ∧ s ∩ -t = ∅

end

-- connected space
class connected_space (α : Type u) extends topological_space α :=
    (clopen_trivial : (∀ s : set α, is_clopen s ↔ (s = univ ∨ s = ∅)))



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
    rw [←closure_eq_interior_iff_clopen], assumption,
    
intro H1, rw [is_clopen] at H1,   
have H2 : closure h1 = h1, from closure_eq_iff_is_closed.mpr H1.right,
have H3 : interior h1 = h1, from interior_eq_iff_open.mpr H1.left,
rw [frontier, H2, H3, diff_eq], simp,  
end


theorem connected_def_empty_frontier_iff_trivial [c : connected_space α] : 
∀ s : set α, frontier s = ∅ ↔ (s = univ ∨ s = ∅) := 
begin
intro s, apply iff.intro, 
assume h1,
  have A : is_clopen s, from (empty_frontier_iff_clopen s).mp h1,
  rw [←connected_space.clopen_trivial], assumption,
assume h2, 
  have B : is_clopen s, from (connected_space.clopen_trivial s).mpr h2,
  rw [empty_frontier_iff_clopen], assumption,  
end


lemma components_of_separation_clopen [topological_space α] 
{U1 U2 : set α} {hu1 : is_open U1} {hu2 : is_open U2}  {H : U1 ∪ U2 = univ ∧ U1 ∩ U2 = ∅ ∧ U1 ≠ ∅ ∧ U2 ≠ ∅}:
is_clopen U1 ∧ is_clopen U2 :=
begin 
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

