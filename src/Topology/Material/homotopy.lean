/-
Copyright (c) 2018 Luca Gerolla. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luca Gerolla, Kevin Buzzard
Definition of homotopy, properties and equivalence relation. 
-/
import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space
import analysis.real
import data.real.basic tactic.norm_num
import data.set.basic
import Topology.Material.pasting_lemma
import Topology.Material.path 
import Topology.Material.real_results


open set filter lattice classical
namespace homotopy  
open path

variables {α  : Type*} [topological_space α ] 
variables {β  : Type*} [topological_space β ] { x y z w : β  }
variables ( x0 : β  )
variable s : I01 

noncomputable theory

local attribute [instance] classical.prop_decidable 

-- HOMOTOPY 


-- General Homotopy 
structure homotopy  {f : α → β} {g : α → β} ( hcf : continuous f) ( hcg : continuous g) :=
(to_fun : I01 × α →  β )  
(at_zero : ( λ x, to_fun ( 0 , x) ) = f )
(at_one : ( λ x, to_fun ( 1 , x) ) = g)
(cont :  continuous  to_fun ) 


structure path_homotopy ( f : path x y) ( g : path x y) := 
(to_fun : I01 × I01 →  β )
(path_s : ∀ s : I01, is_path x y ( λ t, to_fun (s, t) ) ) 
(at_zero : ∀ y, to_fun (0,y) = f.to_fun y ) 
(at_one :  ∀ y, to_fun (1,y) = g.to_fun y)
(cont : continuous to_fun)

-- Simp lemmas
@[simp] 
lemma at_zero_path_hom { f : path x y } { g : path x y} (F : path_homotopy f g) (y : I01) : 
F.to_fun (0, y) = path.to_fun f y := F.3 y

@[simp] 
lemma at_one_path_hom { f : path x y} { g : path x y} (F : path_homotopy f g) (y : I01): 
F.to_fun (1, y) = path.to_fun g y := F.4 y 

@[simp]
lemma at_pt_zero_hom  { f : path x y} { g : path x y} (F : path_homotopy f g) (s : I01) :
F.to_fun (s, 0) = x :=  begin exact (F.2 s).1 end 

@[simp]
lemma at_pt_one_hom  { f : path x y} { g : path x y} (F : path_homotopy f g) (s : I01) :
F.to_fun (s, 1) = y :=  begin exact (F.2 s).2.1  end 



variables { l  k : path x y } 
variable F : path_homotopy l k

-- Alternative path_homotopy.mk
def path_homotopy.mk'  { f : path x y} { g : path x y}  
  (F : I01 × I01 →  β) (start_pt : ∀ s : I01, F (s, 0) = x) (end_pt : ∀ s : I01, F (s, 1) = y) 
  (at_zero : ∀ y, F (0,y) = f.to_fun y ) (at_one : ∀ y, F (1,y) = g.to_fun y ) 
  (F_cont : continuous F) : path_homotopy f g := 
{   to_fun := F, 
    path_s := 
    begin 
      unfold is_path, intro s, split, exact start_pt s, split, exact end_pt s, 
      refine continuous.comp _ F_cont, 
      exact continuous.prod_mk continuous_const continuous_id, 
    end, 
    at_zero := at_zero, 
    at_one := at_one, 
    cont := F_cont
}


 
-- Ending points of path_homotopy are fixed  (Can Remove - not Used)
lemma hom_eq_of_pts { x y : β } { f g : path x y } ( F : path_homotopy f g ) : 
∀ s : I01, check_pts x y ( λ t,  F.to_fun (s, t)) := 
begin 
  intro s, unfold check_pts, split, 
    have h₁ : F.to_fun (s, 0) =  ( λ t,  F.to_fun (s, t)) 0, by simp, 
    rw h₁ , exact (F.path_s s).left,
    have h₂  : F.to_fun (s, 1) =  ( λ t,  F.to_fun (s, t)) 1, by simp, 
    rw h₂ , exact (F.path_s s).right.left 
end 

--- (Can Remove - not Used)
lemma hom_path_is_cont { x y : β } { f g : path x y } ( F : path_homotopy f g ) : 
∀ s : I01, continuous ( λ t,  F.to_fun (s, t)) := 
begin intro s, exact (F.path_s s).right.right end 

def hom_to_path { f g : path x y } ( F : path_homotopy f g ) (s : I01) : path x y := 
to_path ( λ t,  F.to_fun (s, t)) (F.path_s s) 

--------------------------------------------

--------------------------------------------
-- IDENTITY / INVERSE / COMPOSITION of HOMOTOPY 


--- Identity homotopy 
def path_homotopy_id { x y : β} (f : path x y) : path_homotopy f f := 
{   to_fun :=  λ st  , f.to_fun (prod.snd st) ,  

    path_s := begin  intro s, unfold is_path, exact ⟨ f.at_zero,  f.at_one, f.cont ⟩ end, 

    at_zero := by simp , 
    at_one := by simp ,  

    cont := 
    begin 
      let h := λ st, f.to_fun ( @prod.snd I01 I01 st ) , 
      have hc : continuous h, 
        exact continuous.comp  continuous_snd f.cont, 
      exact hc,
    end  
} 

--- Inverse homotopy
lemma help_hom_inv : (λ (st : ↥I01 × ↥I01), F.to_fun (par_inv (st.fst), st.snd)) = 
  ((λ (st : ↥I01 × ↥I01), F.to_fun (st.fst , st.snd)) ∘ 
     (λ (x : I01 × I01) , (( par_inv x.1 , x.2 ) : I01 × I01))) := by trivial

def path_homotopy_inverse { x y : β} {f : path x y} {g : path x y} ( F : path_homotopy f g) : path_homotopy g f := 
{   to_fun :=   λ st  , F.to_fun ( par_inv st.1 , st.2 ),
    path_s := 
    begin 
      intro s, unfold is_path, split, 
        exact (F.path_s (par_inv s)).1, split, 
          exact (F.path_s (par_inv s)).2.1, 
          exact (F.path_s (par_inv s)).2.2
    end,  
    at_zero := begin intro t,  simp [eqn_1_par_inv],  end, 
    at_one := begin intro t, simp, end,   
    cont := 
    begin 
      show continuous ((λ (st : ↥I01 × ↥I01), F.to_fun (st.fst , st.snd)) ∘ (λ (x : I01 × I01) , (( par_inv x.1 , x.2 ) : I01 × I01))), 
      have H : continuous (λ (x : I01 × I01) , (( par_inv x.1 , x.2 ) : I01 × I01)),
        { exact continuous.prod_mk ( continuous.comp  continuous_fst continuous_par_inv) 
          ( @continuous.comp (I01×I01) I01 I01 _ _ _ (λ x : I01×I01, x.2) _ continuous_snd continuous_id) }, 
      simp [continuous.comp H F.cont], 
    end 
} 

------------------------------------------

---- Composition of homotopy

local notation `I` := @set.univ I01

-- Prove T1 × I01, T2 × I01 cover I01 × I01 
lemma cover_prod_I01 : ( (set.prod T1 (@set.univ I01)) ∪ (set.prod T2 (@set.univ I01)) ) = 
  @set.univ (I01 × I01) := 
begin 
  apply set.ext, intro x, split, simp [mem_set_of_eq], 
  intro H, simp, have H : 0 ≤ x.1.val ∧ x.1.val ≤ 1, by exact x.1.property,
  unfold T1 T2 T, simp [mem_set_of_eq, or_iff_not_imp_left, -one_div_eq_inv], 
  intro nL, have H2 : (1 / 2 :ℝ )< x.1.val, by exact nL H.1, 
  exact ⟨ le_of_lt H2, H.2 ⟩ ,
end

-- Closedness and intersection of T1 × I01, T2 × I01
lemma prod_T1_is_closed : is_closed (set.prod T1 I) := 
begin simp [T1_is_closed, is_closed_prod]  end

lemma prod_T2_is_closed : is_closed (set.prod T2 I) := 
begin simp [T2_is_closed, is_closed_prod] end

lemma prod_inter_T : set.inter (set.prod T1 I) (set.prod T2 I) = 
  set.prod  { x : I01 | x.val = 1/2 } I := 
begin 
  unfold T1 T2 T set.inter set.prod, simp [mem_set_of_eq, -one_div_eq_inv], 
  apply set.ext, intro x, split,
  {rw mem_set_of_eq , rw mem_set_of_eq, simp [-one_div_eq_inv], intros A B C D, 
   have H : x.1.val < 1 / 2 ∨ x.1.val = 1/2, by exact lt_or_eq_of_le B, 
   exact le_antisymm  B C   }, 
  rw mem_set_of_eq , rw mem_set_of_eq, intro H, rw H, norm_num 
end


-- Define general / T1 / T2 reparametrised homotopy and prove continuity
def fgen_hom { x y : α } {r s : ℝ} {f g: path x y } (Hrs : r < s)
 ( F : path_homotopy f g) : (set.prod (T r s Hrs ) I) → α := 
λ st, F.to_fun (( par Hrs ⟨st.1.1, (mem_prod.1 st.2).1 ⟩) , st.1.2 )


theorem p_hom_cont { x y : α } {r s : ℝ} {f g : path x y } (Hrs : r < s) ( F : path_homotopy f g)  : continuous (fgen_hom Hrs F) := 
begin 
  unfold fgen_hom, refine continuous.comp _ F.cont , 
  refine continuous.prod_mk _ (continuous.comp continuous_subtype_val continuous_snd), 
  refine continuous.comp _ (continuous_par Hrs), 
  refine continuous_subtype_mk _ _,
  exact continuous.comp continuous_subtype_val continuous_fst,
end

def fa_hom { x y : α }{f g: path x y } ( F : path_homotopy f g) : (set.prod T1 I) → α  := 
@fgen_hom _ _ _ _ 0 (1/2 : ℝ ) _ _  T1._proof_1 F 

lemma CA_hom { x y : α }{f g: path x y } ( F : path_homotopy f g) : continuous (fa_hom F) := 
p_hom_cont T1._proof_1 F 
 
def fb_hom { x y : α }{f g: path x y } ( F : path_homotopy f g) : (set.prod T2 I) → α  := 
@fgen_hom _ _ _ _ (1/2 : ℝ ) 1 _ _  T2._proof_1 F 

lemma CB_hom { x y : α }{f g: path x y } ( F : path_homotopy f g) : continuous (fb_hom F) := 
p_hom_cont T2._proof_1 F 

---

-- Other helpful lemmas 

@[simp]
lemma cond_start {f : path x y} {g : path x y} {h : path x y} 
  ( F : path_homotopy f g) ( G : path_homotopy g h) : 
  paste cover_prod_I01 (fa_hom F) (fb_hom G) (s, 0) = x := 
begin unfold paste, split_ifs, unfold fa_hom fgen_hom, simp, unfold fb_hom fgen_hom, simp, end

@[simp]
lemma cond_end {f : path x y} {g : path x y} {h : path x y} 
  ( F : path_homotopy f g) ( G : path_homotopy g h) : 
  paste cover_prod_I01 (fa_hom F) (fb_hom G) (s, 1) = y := 
begin unfold paste, split_ifs, unfold fa_hom fgen_hom, simp, unfold fb_hom fgen_hom, simp, end

-- Homotopy composition
def path_homotopy_comp  {f : path x y} {g : path x y} {h : path x y} 
  ( F : path_homotopy f g) ( G : path_homotopy g h) : path_homotopy f h :=
{   to_fun := λ st, ( @paste (I01 × I01) β (set.prod T1 I) (set.prod T2 I)  cover_prod_I01 ( λ st , (fa_hom F ) st ) ) ( λ st, (fb_hom G ) st  )  st  , 

    path_s := 
    begin 
      intro s, unfold is_path, split, simp, 
        split, simp, simp, 
        
      unfold paste, unfold fa_hom fb_hom fgen_hom, simp, 
      by_cases H : ∀ t : I01, (s, t) ∈ set.prod T1 I, simp [H],  
        refine (F.path_s (par T1._proof_1 ⟨ s, _ ⟩  )).2.2, unfold set.prod at H, 
        have H2 : (s, s) ∈ {p : ↥I01 × ↥I01 | p.fst ∈ T1 ∧ p.snd ∈ univ}, exact H s, simp [mem_set_of_eq] at H2, exact H2, 
        simp at H,
        have H3:  s ∉ T1, simp [not_forall] at H, exact H.2,
        simp [H3], refine (G.path_s (par T2._proof_1 ⟨ s, _ ⟩  )).2.2,        
        exact T2_of_not_T1 H3, 
    end,  

    at_zero := begin  intro y, simp, unfold paste, rw dif_pos, unfold fa_hom fgen_hom, simp , 
        simp [mem_set_of_eq], exact help_T1,  end, 

    at_one := begin intro y, simp, unfold paste, rw dif_neg, unfold fb_hom fgen_hom, simp , 
        simp [mem_set_of_eq], exact help_02, end,  

    cont := 
    begin simp, refine cont_of_paste _ _ _ (CA_hom F) (CB_hom G) , 
      exact prod_T1_is_closed, 
      exact prod_T2_is_closed, 
      unfold match_of_fun, intros x B1 B2, 
        have Int : x ∈ set.inter (set.prod T1 I) (set.prod T2 I), exact ⟨ B1 , B2 ⟩ , 
        rwa [prod_inter_T] at Int, 
        have V : x.1.1 = 1/2, rwa [set.prod, mem_set_of_eq] at Int, rwa [mem_set_of_eq] at Int, exact Int.1, cases x, 
        have xeq : x_fst = ⟨ 1/2 , help_01 ⟩ , apply subtype.eq, rw V,
        simp [xeq, -one_div_eq_inv], 
        show fa_hom F ⟨(⟨1 / 2, help_01⟩, x_snd), _⟩ = fb_hom G ⟨(⟨1 / 2, help_01⟩, x_snd), _⟩ , unfold fa_hom fb_hom fgen_hom, 
        simp [eqn_1, eqn_2, -one_div_eq_inv], 
    end 
}  

---------------------------------

------------------------------------------------------

---- EQUIVALENCE OF HOMOTOPY



definition is_homotopic_to  (f : path x y) ( g : path x y) : Prop := nonempty ( path_homotopy f g) 


theorem is_reflexive : @reflexive (path x y) ( is_homotopic_to ) := 
begin 
  unfold reflexive, intro f, unfold is_homotopic_to,   
    have H : path_homotopy f f, 
        exact path_homotopy_id f , 
    exact ⟨ H ⟩ 
end


theorem is_symmetric  : @symmetric (path x y)  (is_homotopic_to) :=
begin
    unfold symmetric, intros f g H, unfold is_homotopic_to,
    cases H with F, exact ⟨path_homotopy_inverse  F⟩,
end

theorem is_transitive  : @transitive (path x y)  (is_homotopic_to) := 
begin 
    unfold transitive, intros f g h Hfg Hgh, unfold is_homotopic_to at *, 
      cases Hfg  with F,  cases Hgh with G,  
    exact ⟨ path_homotopy_comp F G⟩ , 
end 


theorem is_equivalence : @equivalence (path x y)  (is_homotopic_to) := 
⟨ is_reflexive, is_symmetric, is_transitive⟩ 


-----------------------------------------------------



end homotopy