import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space
import analysis.real
import data.real.basic tactic.norm_num
import data.set.basic
import Topology.Material.subsets
import Topology.Material.path 


open set filter lattice classical
namespace homotopy  
open path

variables {α  : Type*} [topological_space α ] 
variables {β  : Type*} [topological_space β ] { x y  z w : β  }
variables ( x0 : β  )
variable s : I01 

noncomputable theory

def P := topological_space (I01 × α )

-- HOMOTOPY 

-- General Homotopy 
structure homotopy {α} {β} [topological_space α] [topological_space β] (f : α → β)
( hcf : continuous f) (g : α → β) ( hcg : continuous g) :=
(to_fun : I01 × α →  β ) -- for product topology 
(at_zero : ( λ x, to_fun ( 0 , x) ) = f )
(at_one : ( λ x, to_fun ( 1 , x) ) = g)
(cont :  continuous  to_fun )   -- w.r.t product topology 



structure path_homotopy {β} [topological_space β] { x y : β } ( f : path x y) ( g : path x y) := 
(to_fun : I01 × I01 →  β )
(path_s : ∀ s : I01, is_path x y ( λ t, to_fun (s, t) ) ) 
(at_zero : ∀ y, to_fun (0,y) = f.to_fun y ) 
(at_one :  ∀ y, to_fun (1,y) = g.to_fun y)
(cont : continuous to_fun)

@[simp] 
lemma at_zero_path_hom {β} [topological_space β] { x y : β } { f : path x y} { g : path x y} {F : path_homotopy f g} (y : I01) : 
F.to_fun (0, y) = path.to_fun f y := F.3 y

@[simp] 
lemma at_one_path_hom {β} [topological_space β] { x y : β } { f : path x y} { g : path x y} {F : path_homotopy f g} (y : I01) : 
F.to_fun (1, y) = path.to_fun g y := F.4 y 

@[simp]
lemma at_pt_zero_hom {β} [topological_space β] { x y : β } { f : path x y} { g : path x y} {F : path_homotopy f g} (s : I01) :
F.to_fun (s, 0) = x :=  begin exact (F.2 s).1 end 

@[simp]
lemma at_pt_one_hom {β} [topological_space β] { x y : β } { f : path x y} { g : path x y} {F : path_homotopy f g} (s : I01) :
F.to_fun (s, 1) = y :=  begin exact (F.2 s).2.1  end 


/- Alternative definitions
structure path_homotopy2 {β} [topological_space β] { x y : β } ( f : path x y) ( g : path x y) := 
(to_fun : I01 ×  I01 →  β )
(path_s : ∀ s : I01,  to_fun (s ,0) = x ∧ to_fun (s, 1) = y  ) 
(at_zero : ∀ y, to_fun 0 y = f.to_fun y ) 
(at_one :  ∀ y, to_fun 1 y = g.to_fun y)
(cont : continuous to_fun)

structure path_homotopy3 {β} [topological_space β] { x y : β } ( f : path x y) ( g : path x y) := 
(to_fun : I01 → I01 →  β )
(path_s : ∀ s : I01, is_path x y ( λ t, to_fun s t ) )  -- ∀ s, points match and continuous (λ t, to_fun s t )
(at_zero : to_fun 0  = f.to_fun  ) 
(at_one :  to_fun 1  = g.to_fun )
(cont : continuous to_fun) -/ 


variables ( l : path x y) (k : path x y)
variable F : path_homotopy l k

def path_homotopy.mk' {β} [topological_space β] { x y : β } { f : path x y} { g : path x y}  
(F : I01 × I01 →  β) (start_pt : ∀ s : I01, F (s, 0) = x) (end_pt : ∀ s : I01, F (s, 1) = y) 
(at_zero : ∀ y, F (0,y) = f.to_fun y ) (at_one : ∀ y, F (1,y) = g.to_fun y ) (F_cont : continuous F) : 
path_homotopy f g := 
{   to_fun := F, 
    path_s := begin unfold is_path, intro s, split, exact start_pt s, split, exact end_pt s, 
        refine continuous.comp _ _, exact continuous.prod_mk continuous_const continuous_id, exact F_cont, 
    end,
    at_zero := at_zero, 
    at_one := at_one, 
    cont := F_cont

}



def hom_to_path { x y : β } { f g : path x y } 
( F : path_homotopy f g ) (s : I01) : path x y := 
to_path ( λ t,  F.to_fun (s, t)) (F.path_s s) 
 
-- Ending points of path_homotopy are fixed  (Can Remove - not Used)
lemma hom_eq_of_pts { x y : β } { f g : path x y } ( F : path_homotopy f g ) : 
∀ s : I01, check_pts x y ( λ t,  F.to_fun (s, t)) := 
begin 
    intro s, unfold check_pts, split, 
        have H1: F.to_fun (s, 0) =  ( λ t,  F.to_fun (s, t)) 0,
            simp, 
        rw H1, exact (F.path_s s).left,
        have H1: F.to_fun (s, 1) =  ( λ t,  F.to_fun (s, t)) 1,
            simp, 
        rw H1, exact (F.path_s s).right.left 
end 

--- (Can Remove - not Used)
lemma hom_path_is_cont { x y : β } { f g : path x y } ( F : path_homotopy f g ) : 
∀ s : I01, continuous ( λ t,  F.to_fun (s, t)) := 
begin 
intro s, exact (F.path_s s).right.right 
end 


--------------------------------------------
-- IDENTITY / INVERSE / COMPOSITION of HOMOTOPY 


--- Identity homotopy 
def path_homotopy_id { x y : β} (f : path x y) : path_homotopy f f := 
{   to_fun :=  λ st  , f.to_fun (prod.snd st) ,  
    path_s := begin  intro s, unfold is_path, 
    exact ⟨ f.at_zero,  f.at_one, f.cont ⟩ end, 
    at_zero := by simp , 
    at_one := by simp ,  
    cont := begin 
    let h := λ st, f.to_fun ( @prod.snd I01 I01 st ) , 
    have hc : continuous h, 
        exact continuous.comp  continuous_snd f.cont, 
    exact hc,
    end  
} 

--- Inverse homotopy
lemma help_hom_inv : (λ (st : ↥I01 × ↥I01), F.to_fun (par_inv (st.fst), st.snd)) = ((λ (st : ↥I01 × ↥I01), F.to_fun (st.fst , st.snd)) ∘ (λ (x : I01 × I01) , (( par_inv x.1 , x.2 ) : I01 × I01))) := 
begin trivial, end 

def path_homotopy_inverse { x y : β} {f : path x y} {g : path x y} ( F : path_homotopy f g) : path_homotopy g f := 
{   to_fun :=   λ st  , F.to_fun ( par_inv st.1 , st.2 ),
    path_s := begin 
    intro s, unfold is_path, split, 
        exact (F.path_s (par_inv s)).1, split, 
          exact (F.path_s (par_inv s)).2.1, 
            exact (F.path_s (par_inv s)).2.2
    end,  
    at_zero := begin intro t,  simp [eqn_1_par_inv],    end, --exact F.at_one t
    at_one := begin intro t, simp, end,   --exact F.at_zero t 
    cont := begin 
    show continuous ((λ (st : ↥I01 × ↥I01), F.to_fun (st.fst , st.snd)) ∘ (λ (x : I01 × I01) , (( par_inv x.1 , x.2 ) : I01 × I01))), 
    have H : continuous (λ (x : I01 × I01) , (( par_inv x.1 , x.2 ) : I01 × I01)),
      exact continuous.prod_mk ( @continuous.comp (I01×I01) I01 I01 _ _ _ (λ x : I01×I01, x.1) _ continuous_fst continuous_par_inv) ( @continuous.comp (I01×I01) I01 I01 _ _ _ (λ x : I01×I01, x.2) _ continuous_snd continuous_id),
    simp [continuous.comp H F.cont], 
    end 
} 


---- Composition of homotopy

local notation `I` := @set.univ I01

lemma cover_prod_I01 : ( (set.prod T1 (@set.univ I01)) ∪  (set.prod T2 (@set.univ I01)) ) = @set.univ (I01 × I01) := 
begin apply set.ext, intro x, split, 
  simp [mem_set_of_eq], 
  intro H, simp, have H : 0≤ x.1.val ∧ x.1.val ≤ 1, exact x.1.property, unfold T1 T2 T, simp [mem_set_of_eq, or_iff_not_imp_left, -one_div_eq_inv], 
  intro nL, have H2 : (1 / 2 :ℝ )< x.1.val, exact nL H.1, exact ⟨ le_of_lt H2, H.2 ⟩ ,
end


def fgen_hom {α } [topological_space α ] { x y : α }{r s : ℝ}{f g: path x y } (Hrs : r < s)
 ( F : path_homotopy f g) : (set.prod (T r s Hrs ) I) → α := 
λ st, F.to_fun (( par Hrs ⟨st.1.1, (mem_prod.1 st.2).1 ⟩) , st.1.2 )


theorem p_hom_cont {α } [topological_space α ]{ x y : α }{r s : ℝ} {f g : path x y } (Hrs : r < s) ( F : path_homotopy f g)  : continuous (fgen_hom Hrs F) := 
begin unfold fgen_hom,
 refine continuous.comp _ F.cont , 
 refine continuous.prod_mk _ (continuous.comp continuous_subtype_val continuous_snd), 
 refine continuous.comp _ (continuous_par Hrs), 
 refine continuous_subtype_mk _ _,
 exact continuous.comp continuous_subtype_val continuous_fst,
end


def fa_hom { x y : α }{f g: path x y } ( F : path_homotopy f g) : (set.prod T1 I) → α  := @fgen_hom _ _ _ _ 0 (1/2 : ℝ ) _ _  T1._proof_1 F 

lemma CA_hom { x y : α }{f g: path x y } ( F : path_homotopy f g) : continuous (fa_hom F) := p_hom_cont T1._proof_1 F 
 
def fb_hom { x y : α }{f g: path x y } ( F : path_homotopy f g) : (set.prod T2 I) → α  := @fgen_hom _ _ _ _ (1/2 : ℝ ) 1 _ _  T2._proof_1 F 

lemma CB_hom { x y : α }{f g: path x y } ( F : path_homotopy f g) : continuous (fb_hom F) := p_hom_cont T2._proof_1 F 

lemma help_hom_1 {s t : I01} (H : s ∈ T1) : (s, t) ∈ set.prod T1 I := by simpa

lemma prod_T1_is_closed : is_closed (set.prod T1 I) := begin simp [T1_is_closed, is_closed_prod]  end

lemma prod_T2_is_closed : is_closed (set.prod T2 I) := begin simp [T2_is_closed, is_closed_prod] end

lemma prod_inter_T : set.inter (set.prod T1 I) (set.prod T2 I) = set.prod  { x : I01 | x.val = 1/2 } I := 
begin unfold T1 T2 T set.inter set.prod, simp [mem_set_of_eq, -one_div_eq_inv], apply set.ext, intro x, split,
  {rw mem_set_of_eq , rw mem_set_of_eq, simp [-one_div_eq_inv], intros A B C D, have H : x.1.val < 1 / 2 ∨ x.1.val = 1/2, 
        exact  lt_or_eq_of_le B, exact le_antisymm  B C,    
  }, { rw mem_set_of_eq , rw mem_set_of_eq, intro H, rw H, norm_num }
end


local attribute [instance] classical.prop_decidable 

@[simp]
lemma cond_start { x y : β} {f : path x y} {g : path x y} {h : path x y} 
( F : path_homotopy f g) ( G : path_homotopy g h) : paste cover_prod_I01 (fa_hom F) (fb_hom G) (s, 0) = x := 
begin  unfold paste, split_ifs, unfold fa_hom fgen_hom, simp, unfold fb_hom fgen_hom, simp, end

@[simp]
lemma cond_end { x y : β} {f : path x y} {g : path x y} {h : path x y} 
( F : path_homotopy f g) ( G : path_homotopy g h) : paste cover_prod_I01 (fa_hom F) (fb_hom G) (s, 1) = y := 
begin unfold paste, split_ifs, unfold fa_hom fgen_hom, simp, unfold fb_hom fgen_hom, simp, end

lemma part_CA_hom { x y : α }{f g: path x y } ( F : path_homotopy f g) (s : I01) (H : s ∈ T1) : continuous (λ (t: ↥I01), (fa_hom F) ⟨ (s, t), (help_hom_1 H ) ⟩   ) := 
begin unfold fa_hom fgen_hom, simp, exact (F.path_s (par T1._proof_1 ⟨ s, H ⟩  )).2.2, 
end

lemma T2_of_not_T1 { s : I01} : (s ∉ T1) → s ∈ T2 := 
begin intro H, have H2 : T1 ∪ T2 = @set.univ I01, exact cover_I01, unfold T1 T2 T at *, simp [-one_div_eq_inv],
 rw mem_set_of_eq at H, rw not_and at H, have H3 : 1/2 < s.val, have H4 : ¬s.val ≤ 1 / 2, exact  H (s.2.1), exact lt_of_not_ge H4,
 exact ⟨ le_of_lt H3, s.2.2⟩ , 
end

--set_option trace.simplify.rewrite true
def path_homotopy_comp { x y : β} {f : path x y} {g : path x y} {h : path x y} ( F : path_homotopy f g) ( G : path_homotopy g h) : 
path_homotopy f h :=
{   to_fun := λ st, ( @paste (I01 × I01) β (set.prod T1 I) (set.prod T2 I)  cover_prod_I01 ( λ st , (fa_hom F ) st ) ) ( λ st, (fb_hom G ) st  )  st  , 

    path_s := begin intro s, unfold is_path, split, 
        simp, --exact cond_start s F G,
        split,  ---exact cond_end s F G,
        simp, simp, --refine cont_of_paste cover_prod_I01  prod_T1_is_closed prod_T2_is_closed (part_CA_hom F s _) _, 
        
        unfold paste, unfold fa_hom fb_hom fgen_hom, simp,  --rw  (F.path_s (par T1._proof_1 s)).2.2 , 
        by_cases H : ∀ t : I01, (s, t) ∈ set.prod T1 I, simp [H],  
          refine (F.path_s (par T1._proof_1 ⟨ s, _ ⟩  )).2.2, unfold set.prod at H, 
          have H2 : (s, s) ∈ {p : ↥I01 × ↥I01 | p.fst ∈ T1 ∧ p.snd ∈ univ}, exact H s, simp [mem_set_of_eq] at H2, exact H2, 
          simp at H,
          have H3:  s ∉ T1, simp [not_forall] at H, exact H.2,
          simp [H3], refine (G.path_s (par T2._proof_1 ⟨ s, _ ⟩  )).2.2,        
          exact T2_of_not_T1 H3, 
           --simp [mem_set_of_eq]  at H, 
        --exact F.cont, 
        end,  

    at_zero := begin  intro y, simp, unfold paste, rw dif_pos, unfold fa_hom fgen_hom, simp , 
        simp [mem_set_of_eq], exact help_T1,  end, 

    at_one := begin intro y, simp, unfold paste, rw dif_neg, unfold fb_hom fgen_hom, simp , 
        simp [mem_set_of_eq], exact help_02, end,  

    cont := begin simp, refine cont_of_paste _ _ _ (CA_hom F) (CB_hom G) , 
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



definition is_homotopic_to { x y : β } (f : path x y) ( g : path x y) : Prop := nonempty ( path_homotopy f g) 

--definition is_homotopic_to' { x y : β } (f : path x y) ( g : path x y) : Prop := ∃ (F : Type*) , F = path_homotopy f g -- without nonempty

theorem is_reflexive {β  : Type*} [topological_space β ] { x y : β  } : @reflexive (path x y) ( is_homotopic_to ) := 
begin 
  unfold reflexive, intro f, unfold is_homotopic_to,   
    have H : path_homotopy f f, 
        exact path_homotopy_id f , 
    exact ⟨ H ⟩ 
end


theorem is_symmetric {β  : Type*} [topological_space β ] { x y : β  } : @symmetric (path x y)  (is_homotopic_to) :=
begin
    unfold symmetric, intros f g H, unfold is_homotopic_to,
    cases H with F, exact ⟨path_homotopy_inverse  F⟩,
end

theorem is_transitive {β  : Type*} [topological_space β ] { x y : β  } : @transitive (path x y)  (is_homotopic_to) := 
begin 
    unfold transitive, intros f g h Hfg Hgh, unfold is_homotopic_to at *, 
      cases Hfg  with F,  cases Hgh with G,  
    exact ⟨ path_homotopy_comp F G⟩ , 
end 

theorem is_equivalence : @equivalence (path x y)  (is_homotopic_to) := 
⟨ is_reflexive, is_symmetric, is_transitive⟩ 


-----------------------------------------------------

-----------------------------------------------------

---- OTHER RESULTS (for FUNDAMETAL GROUP)


---- Reparametrisation of path and homotopies 

-- (Formalise paragraph 2 pg 27 of AT, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf )

structure repar_I01  := 
(to_fun : I01 → I01 )
(at_zero : to_fun 0 = 0 )
(at_one : to_fun 1 = 1 )
(cont : continuous to_fun )

@[simp]
lemma repar_I01_at_zero (f : repar_I01) : f.to_fun 0 = 0 := f.2

@[simp]
lemma repar_I01_at_one ( f  : repar_I01) : f.to_fun 1 = 1 := f.3

def repar_path {α : Type*} [topological_space α ] {x y : α } ( f : path x y)( φ : repar_I01 ) : path x y := 
{   to_fun := λ t , f.to_fun ( φ.to_fun t) ,  
    at_zero := by simp, 
    at_one := by simp, 
    cont := continuous.comp φ.cont f.cont
}


def rep_hom (φ : repar_I01) : I01 × I01 → I01 := λ st, ⟨ ((1 : ℝ ) - st.1.1)*(φ.to_fun st.2).1 + st.1.1 * st.2.1,  
begin unfold I01, rw mem_set_of_eq, split, 
    { suffices H1 : 0 ≤ (1 - (st.fst).val) * (φ.to_fun (st.snd)).val , 
      suffices H2 : 0 ≤ (st.fst).val * (st.snd).val, exact add_le_add H1 H2, 
        refine mul_nonneg _ _, exact st.1.2.1, exact st.2.2.1, 
        refine mul_nonneg _ _, show 0 ≤ 1 - (st.fst).val , refine sub_nonneg.2  _ , exact st.1.2.2, exact (φ.to_fun (st.snd)).2.1, 
    }, rw (@mul_comm _ _ (1 - (st.fst).val)  (φ.to_fun (st.snd)).val), simp [@mul_add ℝ _ ((φ.to_fun (st.snd)).val )  (1:ℝ ) (- st.fst.val) ], 
    rw mul_comm ((φ.to_fun (st.snd)).val ) ((st.fst).val), 
    have H : ((st.fst).val * (st.snd).val + -((st.fst).val * (φ.to_fun (st.snd)).val)) = (st.fst).val * ((st.snd).val - ((φ.to_fun (st.snd)).val)), simp [mul_add], 
    rw H, have H2 : (st.fst).val ≤ 1, exact st.1.2.2,  
    let C := 0 < ((st.snd).val - (φ.to_fun (st.snd)).val) , 
    by_cases C, 
        have C1 : 0 < ((st.snd).val - (φ.to_fun (st.snd)).val), exact h, 
        have H3 : (st.fst).val * ((st.snd).val - (φ.to_fun (st.snd)).val) ≤ 1 * ((st.snd).val - (φ.to_fun (st.snd)).val), rw one_mul, 
            refine (@le_div_iff _ _ (st.fst).val ((st.snd).val - (φ.to_fun (st.snd)).val) ((st.snd).val - (φ.to_fun (st.snd)).val) C1).1 _, 
            have h2 : ((st.snd).val - (φ.to_fun (st.snd)).val) / ((st.snd).val - (φ.to_fun (st.snd)).val) = 1, refine div_self _, exact ne_of_gt C1,
            rw h2, exact st.1.2.2,  rw one_mul at H3,  
        have G1 : (φ.to_fun (st.snd)).val + (st.fst).val * ((st.snd).val - (φ.to_fun (st.snd)).val) ≤ (φ.to_fun (st.snd)).val + ((st.snd).val - (φ.to_fun (st.snd)).val), 
            refine add_le_add _ H3, refine le_of_eq _, refl, 
        suffices G2 : (φ.to_fun (st.snd)).val + ((st.snd).val - (φ.to_fun (st.snd)).val) ≤ 1, exact le_trans G1 G2, 
            simp [st.2.2.2], 
        -----
        have C0 : ¬ 0 < ((st.snd).val - (φ.to_fun (st.snd)).val), exact h, 
        have C1 : ((st.snd).val - (φ.to_fun (st.snd)).val) ≤ 0, exact not_lt.1 C0, 
        have H3 : (st.fst).val * ((st.snd).val - (φ.to_fun (st.snd)).val) ≤ 0, 
            exact mul_nonpos_of_nonneg_of_nonpos (st.1.2.1) C1,
        have G1 : (φ.to_fun (st.snd)).val + (st.fst).val * ((st.snd).val - (φ.to_fun (st.snd)).val) ≤ (φ.to_fun (st.snd)).val , 
            refine le_neg_add_iff_add_le.1 _, simpa ,
        have G2 : (φ.to_fun (st.snd)).val ≤ 1, exact (φ.to_fun (st.snd)).2.2, 
        exact le_trans G1 G2, 

    --( 1-s )φ t + s t =
    -- φ t + s (t - φ t) ≤ 
    -- φ t + (t - φ t) =
    -- t ≤ 1 

end ⟩ 

@[simp]
lemma rep_hom_at_zero {φ : repar_I01} ( y : I01) : rep_hom φ (0, y) = φ.to_fun y := 
begin unfold rep_hom, simp, apply subtype.eq, simp [mul_comm, mul_zero], 
  show  y.val * 0 + (φ.to_fun y).val * (1 + -0) = (φ.to_fun y).val, simp [mul_zero, mul_add, add_zero] 
end

@[simp]
lemma rep_hom_at_one {φ : repar_I01} ( y : I01) : rep_hom φ (1, y) =  y := 
begin unfold rep_hom, apply subtype.eq, simp [-sub_eq_add_neg],
  show  1 * y.val + (1 - 1) * (φ.to_fun y).val = y.val, simp
end 

@[simp]
lemma rep_hom_pt_at_zero {φ : repar_I01} ( s : I01) : rep_hom φ (s, 0) = 0 := 
begin unfold rep_hom, simp, apply subtype.eq, simp,  show s.val * 0+ (1 + -s.val) * 0 = 0, simp, end

@[simp]
lemma rep_hom_pt_at_one {φ : repar_I01} ( s : I01) : rep_hom φ (s, 1) = 1 := 
begin unfold rep_hom, simp, apply subtype.eq, simp, show s.val * 1 + (1 + -s.val) * 1 = 1, simp end

lemma cont_rep_hom (φ : repar_I01) : continuous (rep_hom φ ) := 
begin unfold rep_hom, refine continuous_subtype_mk _ _, 
refine @continuous_add _ _ _ _ _ _ (λ st: I01×I01 , (1 - (st.fst).val) * (φ.to_fun (st.snd)).val ) _ _ _, 
 { refine continuous_mul _ _, refine continuous_add _ _, exact continuous_const, 
     show continuous (( λ x : ℝ , - x ) ∘ (λ (st : ↥I01 × ↥I01), (st.fst).val) ), 
     refine continuous.comp (continuous.comp continuous_fst continuous_subtype_val) (continuous_neg continuous_id),  
   exact continuous.comp (continuous.comp continuous_snd φ.cont) continuous_subtype_val
 },
   refine continuous_mul _ _ , exact continuous.comp continuous_fst continuous_subtype_val, 
    exact continuous.comp continuous_snd continuous_subtype_val
end

-- Define homotopy from f φ to f , for any repar φ 
def hom_repar_path_to_path {α : Type*} [topological_space α ] {x y : α } ( f : path x y)( φ : repar_I01 ) : path_homotopy (repar_path f φ ) f := 
{   to_fun :=  λ st, f.to_fun ( (rep_hom φ) st), 
    path_s := begin intro s, unfold is_path, split, simp, split, simp, 
      show continuous ( (λ (st : I01×I01), f.to_fun (rep_hom φ st )) ∘ ( λ t : I01, ((s, t) : I01 × I01) )    ),
      refine continuous.comp _ (continuous.comp (cont_rep_hom φ ) f.cont ), 
      exact continuous.prod_mk continuous_const continuous_id 
    end, 
    at_zero := by simp,  
    at_one := by simp,  
    cont :=  continuous.comp (cont_rep_hom φ ) f.cont
}


-- Prove f φ ≈ f (they are homotopic)
theorem repar_path_is_homeq {α : Type*} [topological_space α ] {x y : α } ( f : path x y)( φ : repar_I01 ) 
: is_homotopic_to (repar_path f φ ) f := 
begin unfold is_homotopic_to, exact nonempty.intro (hom_repar_path_to_path f φ ),  end 

------------------------------

-- Homotopy of path inverses
------  a ≈ b  →  a⁻¹ ≈ b⁻¹ 


def f_path_inv {α } [topological_space α] {x y : α} { a b : path x y } ( F : path_homotopy a b ) : I01 × I01 → α :=
λ st, F.to_fun (st.1 , par_inv st.2) 

lemma f_path_inv_start_pt {α } [topological_space α] {x y : α} { a b : path x y } ( F : path_homotopy a b ) :
∀ (s : I01), f_path_inv F (s, 0) = y := begin unfold f_path_inv, simp end

lemma f_path_inv_end_pt {α } [topological_space α] {x y : α} { a b : path x y } ( F : path_homotopy a b ) :
∀ (s : I01), f_path_inv F (s, 1) = x := begin unfold f_path_inv, simp end

lemma f_path_inv_at_zero {α } [topological_space α] {x y : α} { a b : path x y } ( F : path_homotopy a b ) :
∀ (y_1 : I01), f_path_inv F (0, y_1) = (inv_of_path a).to_fun y_1 := 
begin intro y, unfold f_path_inv inv_of_path, simp, end

lemma f_path_inv_at_one {α } [topological_space α] {x y : α} { a b : path x y } ( F : path_homotopy a b ) :
∀ (y_1 : I01), f_path_inv F (1, y_1) = (inv_of_path b).to_fun y_1 := 
begin intro y, unfold f_path_inv inv_of_path, simp, end 

lemma f_path_inv_cont {α } [topological_space α] {x y : α} { a b : path x y } ( F : path_homotopy a b ) :
continuous (f_path_inv F) := 
begin 
 unfold f_path_inv, 
 refine continuous.comp _ F.cont, 
 refine continuous.prod_mk continuous_fst _, 
 exact continuous.comp continuous_snd continuous_par_inv 
end

noncomputable def path_homotopy_of_inv_path {α } [topological_space α] {x y : α} { a b : path x y } 
( F : path_homotopy a b ) : path_homotopy (inv_of_path a) (inv_of_path b) := 
path_homotopy.mk' (f_path_inv F) (f_path_inv_start_pt F) (f_path_inv_end_pt F) (f_path_inv_at_zero F) 
(f_path_inv_at_one F) (f_path_inv_cont F) 


---------------------------------


--------------------------------- 

-- Homotopy on composition of paths 
------ a₁ ≈ b₁ , a₂ ≈ b₂  →  a₁ ⬝ a₂ ≈ b₁ ⬝ b₂ 


-- Define (continuous) shift function to employ results from  path_homotopy_comp
def shift_order ( α : Type* ) (β : Type*) [topological_space α] [topological_space β ] : α × β → β × α := λ ab, (ab.2, ab.1) 

theorem continuous_shift_order {α β } [topological_space α] [topological_space β ] : continuous (shift_order α β ) := 
begin unfold shift_order, exact continuous.prod_mk continuous_snd continuous_fst end 

local notation `shift` := shift_order _ _ 

@[simp]
lemma shift_cond_start { x y : β} { a₁ b₁ : path x y} { a₂  b₂  : path y z} { F : path_homotopy a₁ b₁ } { G : path_homotopy a₂ b₂ } : 
paste cover_prod_I01 (λ (st : ↥(set.prod T1 univ)), F.to_fun (shift ↑st)) (λ (st : ↥(set.prod T2 univ)), G.to_fun (shift ↑st))(shift (s, 0)) = x := 
begin unfold shift_order paste, rw dif_pos, simp, simp, exact help_T1,      end

@[simp]
lemma shift_cond_end { x y : β} { a₁ b₁ : path x y} { a₂  b₂  : path y z} { F : path_homotopy a₁ b₁ } { G : path_homotopy a₂ b₂ } : 
paste cover_prod_I01 (λ (st : ↥(set.prod T1 univ)), F.to_fun (shift ↑st)) (λ (st : ↥(set.prod T2 univ)), G.to_fun (shift ↑st))(shift (s, 1)) = z :=
begin unfold shift_order paste, rw dif_neg, simp, simp, exact help_02,   end

--- 


-- Define (continuous ) reparametrisations to shift domain and construct a homotopy  : a₁ ⬝ a₂ ≈ b₁ ⬝ b₂  
----- by pasting homotopies a₁ ≈ b₁ , a₂ ≈ b₂
def repar_shift_a : set.prod T1 I → I01 × I01 := λ st, shift (  par T1._proof_1 ⟨ st.1.1, (mem_prod.1 st.2).1⟩ , st.1.2 ) 

def repar_shift_b : set.prod T2 I → I01 × I01 := λ st, shift (  par T2._proof_1 ⟨ st.1.1, (mem_prod.1 st.2).1 ⟩ , st.1.2 ) 

lemma cont_r_shift_a : continuous repar_shift_a := 
begin 
unfold repar_shift_a, refine continuous.comp _ continuous_shift_order, refine continuous.prod_mk _ _, 
  refine continuous.comp _ (continuous_par _ ), refine continuous_subtype_mk _ _, exact continuous.comp continuous_subtype_val continuous_fst, 
  exact continuous.comp continuous_subtype_val continuous_snd, 
end

lemma cont_r_shift_b : continuous repar_shift_b := 
begin 
unfold repar_shift_b, refine continuous.comp _ continuous_shift_order, refine continuous.prod_mk _ _, 
  refine continuous.comp _ (continuous_par _ ), refine continuous_subtype_mk _ _, exact continuous.comp continuous_subtype_val continuous_fst, 
  exact continuous.comp continuous_subtype_val continuous_snd, 
end

-- Define the function of homotopy a₁ ⬝ a₂ ≈ b₁ ⬝ b₂ and prove lemmas to use with path_homotopy.mk' 
def f_path_comp {α } [topological_space α] {x y z : α} { a₁ b₁ : path x y} { a₂  b₂  : path y z} ( F : path_homotopy a₁ b₁ ) ( G : path_homotopy a₂ b₂ ) :=
 λ st, ( paste  cover_prod_I01 ( λ st, F.to_fun (repar_shift_a st) ) ( λ st, G.to_fun (repar_shift_b st) ) )  ( shift  st) 

lemma f_path_comp_start_pt {α } [topological_space α] {x y z : α} { a₁ b₁ : path x y} { a₂  b₂  : path y z} ( F : path_homotopy a₁ b₁ ) ( G : path_homotopy a₂ b₂ ) : 
∀ (s : I01), f_path_comp F G (s, 0) = x := 
begin intro s, unfold f_path_comp, unfold repar_shift_a repar_shift_b shift_order paste, rw dif_pos, 
 show F.to_fun (s, par T1._proof_1 ⟨0, help_T1⟩) = x,  simp,  
 simp, exact help_T1,    
end

lemma f_path_comp_end_pt {α } [topological_space α] {x y z : α} { a₁ b₁ : path x y} { a₂  b₂  : path y z} ( F : path_homotopy a₁ b₁ ) ( G : path_homotopy a₂ b₂ ) : 
∀ (s : I01), f_path_comp F G (s, 1) = z := 
begin intro s, unfold f_path_comp, unfold repar_shift_a repar_shift_b shift_order paste, rw dif_neg, simp, 
  show G.to_fun (s, par T2._proof_1 ⟨1, help_T2⟩) = z, simp, 
  simp [help_02],
end

lemma f_path_comp_at_zero {α } [topological_space α] {x y z : α} { a₁ b₁ : path x y} { a₂  b₂  : path y z} ( F : path_homotopy a₁ b₁ ) ( G : path_homotopy a₂ b₂ ) : 
∀ (y : I01), f_path_comp F G (0, y) = (comp_of_path a₁ a₂).to_fun y := 
begin intro s, unfold f_path_comp comp_of_path fa_path fb_path fgen_path paste,  simp, 
split_ifs,  unfold repar_shift_a, unfold shift_order, simpa, 
  { by_contradiction, unfold shift_order at h, simp at h, cc, }, 
  { by_contradiction, unfold shift_order at h, simp at h, cc, }, 
  unfold repar_shift_b, unfold shift_order, simpa,
end

lemma f_path_comp_at_one {α } [topological_space α] {x y z : α} { a₁ b₁ : path x y} { a₂  b₂  : path y z} ( F : path_homotopy a₁ b₁ ) ( G : path_homotopy a₂ b₂ ) : 
 ∀ (y : I01), f_path_comp F G (1, y) = (comp_of_path b₁ b₂).to_fun y := 
begin intro s, unfold f_path_comp comp_of_path fa_path fb_path fgen_path paste,  simp, 
split_ifs,  unfold repar_shift_a, unfold shift_order, simpa, 
  { by_contradiction, unfold shift_order at h, simp at h, cc, }, 
  { by_contradiction, unfold shift_order at h, simp at h, cc, },
  unfold repar_shift_b, unfold shift_order, simpa,
end

lemma f_path_comp_cont {α } [topological_space α] {x y z : α} { a₁ b₁ : path x y} { a₂  b₂  : path y z} ( F : path_homotopy a₁ b₁ ) ( G : path_homotopy a₂ b₂ ) : 
continuous (f_path_comp F G) := 
begin unfold f_path_comp, refine continuous.comp continuous_shift_order _,     
    refine cont_of_paste prod_T1_is_closed prod_T2_is_closed _ _ _, 
    {unfold match_of_fun, intros w B1 B2, 
    have Int : w ∈ set.inter (set.prod T1 I) (set.prod T2 I), exact ⟨ B1 , B2 ⟩ , rwa [prod_inter_T] at Int, 
    have V : w.1.1 = 1/2, rwa [set.prod, mem_set_of_eq] at Int, rwa [mem_set_of_eq] at Int, exact Int.1, cases w, 
    have xeq : w_fst = ⟨ 1/2 , help_01 ⟩ , apply subtype.eq, rw V,
    simp [xeq, -one_div_eq_inv], unfold repar_shift_a repar_shift_b shift_order, 
    simp [-one_div_eq_inv], 
    show F.to_fun (w_snd, par T1._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T1⟩) =
    G.to_fun (w_snd, par T2._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T2⟩) , rw [eqn_1, eqn_2], simp,  
    } ,  
    exact continuous.comp cont_r_shift_a F.cont, 
    exact continuous.comp cont_r_shift_b G.cont, 
end

-- Prove that we have the homotopy a₁ ⬝ a₂ ≈ b₁ ⬝ b₂
noncomputable def path_homotopy_of_comp_path {α } [topological_space α] {x y z : α} { a₁ b₁ : path x y} { a₂  b₂  : path y z} 
( F : path_homotopy a₁ b₁ ) ( G : path_homotopy a₂ b₂ ) : path_homotopy (comp_of_path a₁ a₂) (comp_of_path b₁ b₂) := 
begin 
refine path_homotopy.mk' (f_path_comp F G ) _ _ _ _ _, 
exact f_path_comp_start_pt F G, exact f_path_comp_end_pt F G, 
exact f_path_comp_at_zero F G , exact f_path_comp_at_one F G, 
exact f_path_comp_cont F G, 
end

local attribute [instance] classical.prop_decidable

----------------------------------------------------

--- Extra Result needed later 

lemma frontier_lt_subset_eq [topological_space α] [decidable_linear_order α] [t : ordered_topology α]
  [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) : 
frontier {b | f b < g b} ⊆ {b | f b = g b} :=
begin 
  unfold frontier, 
  have h₁ : interior {b : β | f b < g b} = {b : β | f b < g b}, 
    exact interior_eq_iff_open.2 (is_open_lt  hf hg), rw h₁, 
  have h₂ : closure {b : β | f b < g b} ⊆ closure {b : β | f b ≤  g b}, 
    refine closure_mono _  , rw set.set_of_subset_set_of, intros x h, exact le_of_lt h, 
  have h₃ : closure {b : β | f b ≤  g b} = {b : β | f b ≤  g b}, 
    exact closure_eq_iff_is_closed.2 (is_closed_le hf hg), rw h₃ at h₂ , 
  have g₁ : closure {b : β | f b < g b} \ {b : β | f b < g b} ⊆ 
                 {b : β | f b ≤ g b} \ {b : β | f b < g b}, 
   {unfold has_sdiff.sdiff set.diff, intros a Ha, simp at Ha, simp, 
    cases Ha with a₁ a₂ , 
    have h₄ : a ∈ {b : β | f b ≤ g b}, exact set.mem_of_mem_of_subset a₁ h₂, 
    rw mem_set_of_eq at h₄, exact ⟨ h₄, a₂ ⟩ , }, 
  have g₂ : {b : β | f b ≤ g b} \ {b : β | f b < g b} ⊆ {b : β | f b = g b}, 
    unfold has_sdiff.sdiff set.diff, intros a Ha, simp  at Ha, 
    rw mem_set_of_eq, exact le_antisymm Ha.1 Ha.2, 
  exact set.subset.trans g₁ g₂,  
end

lemma mem_frontier_lt [topological_space α] [decidable_linear_order α] [t : ordered_topology α]
  [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) { s : β  }: 
s ∈ frontier {b | f b < g b}  → s ∈  {b | f b = g b} := 
begin intro h, exact  set.mem_of_mem_of_subset h (frontier_lt_subset_eq hf hg), end 




------------------------------------------

-- Homotopy of composition with inverse 
------ a⁻¹ ⬝ a ≈ c₀  



-- To shrink path f⁻¹ 


def par_aux_a : I01 × I01 → I01 := 
λ st, if ((1 : ℝ ) - st.1.1) < st.2.1 then st.1 else par_inv st.2

-- dite or ite? 


lemma cont_help_1 : continuous (λ (a : ↥I01 × ↥I01), 1 - (a.fst).val ) := 
begin 
 have h : continuous ( λ (r : ℝ ), 1 - r ),  conv in ( (1:ℝ)-_) begin rw help_inv, end,  
  exact continuous.comp (real.continuous_mul_const (-1) ) (real.continuous_add_const 1), 
 exact continuous.comp (continuous.comp continuous_fst continuous_subtype_val) h, 
end

lemma continuous_par_aux_a'  : continuous par_aux_a := 
begin 
unfold par_aux_a, 
refine continuous_if _ continuous_fst _ , 
  { intros st F, 
    have H : frontier {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val} ⊆  {a : ↥I01 × ↥I01 | 1 - (a.fst).val = (a.snd).val }, 
      { unfold frontier , 
        have H2 : interior {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val} = {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val}, 
          refine interior_eq_iff_open.2 _, refine is_open_lt  _ _,  
          exact cont_help_1, 
          exact continuous.comp continuous_snd continuous_subtype_val, 
        rw H2, 
        have H3 : closure {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val} ⊆ closure {a : ↥I01 × ↥I01 | 1 - (a.fst).val ≤ (a.snd).val}, 
          refine closure_mono _  , rw set.set_of_subset_set_of, intros x h, exact le_of_lt h,   
        have H4 : closure {a : ↥I01 × ↥I01 | 1 - (a.fst).val ≤ (a.snd).val} = {a : ↥I01 × ↥I01 | 1 - (a.fst).val ≤ (a.snd).val}, 
          refine closure_eq_iff_is_closed.2 _ ,
          refine is_closed_le cont_help_1 (continuous.comp continuous_snd continuous_subtype_val), 
        rw H4 at H3,  
        have G1 : closure {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val} \ 
          {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val} ⊆ 
          {a : ↥I01 × ↥I01 | 1 - (a.fst).val ≤ (a.snd).val} \ {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val}, 
          { unfold has_sdiff.sdiff set.diff, intros a Ha, simp [-add_neg_le_iff_le_add', -sub_eq_add_neg] at Ha, 
          simp [-add_neg_le_iff_le_add', -sub_eq_add_neg], cases Ha with h₁ h₂ , 
          have h₃ : a ∈ {a : ↥I01 × ↥I01 | 1 - (a.fst).val ≤ (a.snd).val}, exact set.mem_of_mem_of_subset h₁ H3, 
          rw mem_set_of_eq at h₃ , exact ⟨  h₃ , h₂ ⟩ , 
          }, 

        have G2 : {a : ↥I01 × ↥I01 | 1 - (a.fst).val ≤ (a.snd).val} \ {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val} ⊆ 
        {a : ↥I01 × ↥I01 | 1 - (a.fst).val = (a.snd).val}, 
        unfold has_sdiff.sdiff set.diff, intros a Ha, simp [-add_neg_le_iff_le_add', -sub_eq_add_neg] at Ha, 
        rw mem_set_of_eq, exact le_antisymm Ha.1 Ha.2, 
        exact set.subset.trans G1 G2, 
      }, 
    have h : st ∈ {a : ↥I01 × ↥I01 | 1 - (a.fst).val = (a.snd).val}, 
      exact set.mem_of_mem_of_subset F H , 
    rw [ mem_set_of_eq] at h, unfold par_inv, refine subtype.eq _, 
    show (st.fst).val = 1 -(st.snd).val, 
    have H4 : (st.snd).val = 1 - (st.fst).val, exact eq.symm h, 
    simp [H4], 
  }, 
exact continuous.comp continuous_snd continuous_par_inv, 
end

lemma continuous_par_aux_a  : continuous par_aux_a := 
begin 
 unfold par_aux_a, 
 refine continuous_if _ continuous_fst (continuous.comp continuous_snd continuous_par_inv) , 
 intros st F, 
 have H : frontier {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val} ⊆  {a : ↥I01 × ↥I01 | 1 - (a.fst).val = (a.snd).val }, 
   exact frontier_lt_subset_eq cont_help_1 (continuous.comp continuous_snd continuous_subtype_val), 
 have h : st ∈ {a : ↥I01 × ↥I01 | 1 - (a.fst).val = (a.snd).val}, 
   exact set.mem_of_mem_of_subset F H , 
   rw [ mem_set_of_eq] at h, unfold par_inv, refine subtype.eq _, 
   show (st.fst).val = 1 -(st.snd).val, 
   have H4 : (st.snd).val = 1 - (st.fst).val, exact eq.symm h, 
  simp [H4], 
end


def repar_stop_a : set.prod T1 I → I01 := 
λ st, par_aux_a ( shift (  par T1._proof_1 ⟨ st.1.1, (mem_prod.1 st.2).1⟩ , st.1.2 ) )
--- need shift to have st.2 double speed (and re-shift starting domain to keep ordering when constructing homotopy)


lemma cont_r_stop_a : continuous repar_stop_a := 
begin 
 unfold repar_stop_a, refine continuous.comp _ continuous_par_aux_a,
 refine continuous.comp _ continuous_shift_order,
 refine continuous.prod_mk _ (continuous.comp continuous_subtype_val continuous_snd), 
 refine continuous.comp _ (continuous_par _ ),
 refine continuous_subtype_mk _ _, exact continuous.comp continuous_subtype_val continuous_fst, 
end


def fa_inv_comp {α : Type*} [topological_space α ] {x y : α } (f : path x y) : set.prod T1 I → α := 
λ st, f.to_fun  ( repar_stop_a st  )


lemma cont_fa_inv_comp {α : Type*} [topological_space α ] {x y : α } (f : path x y) : 
continuous (fa_inv_comp f) := 
begin unfold fa_inv_comp, exact continuous.comp  cont_r_stop_a  f.cont, end 


--------------

-- To shrink path f 


def par_aux_b : I01 × I01 → I01 := 
λ st, if st.2.1 < st.1.1 then st.1 else st.2



lemma continuous_par_aux_b  : continuous par_aux_b := 
begin 
unfold par_aux_b, 
refine continuous_if _ continuous_fst continuous_snd , 
 {intros st F, 
  have H : frontier {a : ↥I01 × ↥I01 | (a.snd).val < (a.fst).val} ⊆ {a : ↥I01 × ↥I01 | (a.snd).val = (a.fst).val}, 
    exact frontier_lt_subset_eq (continuous.comp continuous_snd continuous_subtype_val) (continuous.comp continuous_fst continuous_subtype_val) , 
  have h : st ∈ {a : ↥I01 × ↥I01 | (a.snd).val = (a.fst).val}, 
   exact set.mem_of_mem_of_subset F H , rw [ mem_set_of_eq] at h, 
   apply eq.symm, exact subtype.eq h,    
 }, 
end


def repar_stop_b : set.prod T2 I → I01  := 
λ st, par_aux_b ( shift (  par T2._proof_1 ⟨ st.1.1, (mem_prod.1 st.2).1⟩ , st.1.2 ) )

lemma cont_r_stop_b : continuous repar_stop_b := 
begin 
 unfold repar_stop_b, refine continuous.comp _ continuous_par_aux_b,
 refine continuous.comp _ continuous_shift_order,
 refine continuous.prod_mk _ (continuous.comp continuous_subtype_val continuous_snd), 
 refine continuous.comp _ (continuous_par _ ),
 refine continuous_subtype_mk _ _, exact continuous.comp continuous_subtype_val continuous_fst, 
end

def fb_inv_comp {α : Type*} [topological_space α ] {x y : α } (f : path x y) : set.prod T2 I → α := 
λ st, f.to_fun (  repar_stop_b st  )

lemma cont_fb_inv_comp {α : Type*} [topological_space α ] {x y : α } (f : path x y) : 
continuous (fb_inv_comp f) := 
begin unfold fb_inv_comp, exact continuous.comp cont_r_stop_b  f.cont, end 



---- Combine 

def f_inv_comp {α : Type*} [topological_space α ] {x y : α } (f : path x y) : I01 × I01 → α := 
λ st, ( paste cover_prod_I01  ( λ st, (fa_inv_comp f ) st ) ( λ st, (fb_inv_comp f ) st ) ) (shift st)
-- see repar_stop_a

lemma f_inv_comp_start_pt {α : Type*} [topological_space α ] {x y : α } (f : path x y) :
 ∀ (s : I01), f_inv_comp f (s, 0) = y := 
begin intro s, 
 unfold f_inv_comp fa_inv_comp fb_inv_comp, unfold repar_stop_a repar_stop_b shift_order par_aux_a par_aux_b paste, simp [-sub_eq_add_neg], 
 rw [dif_pos ], 
 have H : ite (1 - s.val < (par T1._proof_1 ⟨0, help_T1⟩).val) s (par_inv (par T1._proof_1 ⟨0, help_T1⟩)) = (1 : I01), 
    split_ifs,   have H2 : s.val + (0 : I01).val = s.val, show s.val + (0:ℝ ) = s.val, exact  add_zero s.val, 
      have H3 : s.val ≤ (1:I01).val, exact s.2.2, have H4 : 1 - (0:I01).val = 1, exact sub_zero 1, 
      rw [ eqn_start ] at h, rw [sub_lt] at h, have H5 : 1 < s.val, rw H4 at h,  exact h,
      --[sub_lt] at h,    rw [H2] at h, 
      by_contradiction, have G : s.val < s.val, exact lt_of_le_of_lt H3 h, 
        simp [lt_iff_le_and_ne] at G, trivial,
      simp,  
 show f.to_fun (ite (1 - s.val < (par T1._proof_1 ⟨0, help_T1⟩).val) s (par_inv (par T1._proof_1 ⟨0, help_T1⟩))) = y, 
 rw [H], exact f.at_one,
 simp, exact help_T1, 
end


lemma f_inv_comp_end_pt {α : Type*} [topological_space α ] {x y : α } (f : path x y) :
∀ (s : I01), f_inv_comp f (s, 1) = y := 
begin 
 intro s, unfold f_inv_comp, unfold paste, rw dif_neg, unfold fb_inv_comp repar_stop_b shift_order par_aux_b, simp [-sub_eq_add_neg], 
 have H : ite ((par T2._proof_1 ⟨1, help_T2⟩).val < s.val) s (par T2._proof_1 ⟨1, help_T2⟩) = 1,
    split_ifs, {  by_contradiction, rw eqn_end at h, have H2 : s.val ≤ (1:I01).val, exact s.2.2, 
      have G : s.val < s.val, exact lt_of_le_of_lt H2 h, simp [lt_iff_le_and_ne] at G, trivial, 
      },  
      exact eqn_end, 
 show f.to_fun (ite ((par T2._proof_1 ⟨1, help_T2⟩).val < s.val) s (par T2._proof_1 ⟨1, help_T2⟩ )) = y, 
 rw H, exact f.at_one, 
 unfold shift_order, simp [help_02], 
end 


lemma f_inv_comp_at_zero {α : Type*} [topological_space α ] {x y : α } (f : path x y) :
∀ (y_1 : I01), f_inv_comp f (0, y_1) = (comp_of_path (inv_of_path f) f).to_fun y_1 := 
begin 
 intro t, unfold f_inv_comp fa_inv_comp fb_inv_comp repar_stop_a repar_stop_b,  
 unfold paste, unfold shift_order, split_ifs, 
   unfold shift_order at h, simp at h, unfold par_inv comp_of_path paste,  simp [h], 
   unfold fa_path par_aux_a inv_of_path, simp [-sub_eq_add_neg], 
   show f.to_fun (ite (1 - 0< (par T1._proof_1 ⟨t, _⟩).val) 0 (par_inv (par T1._proof_1 ⟨t, _⟩))) =
    f.to_fun (par_inv (par T1._proof_1 ⟨t, _⟩)), 
    simp, rw if_neg, refl, refine not_lt.2 _, exact (par T1._proof_1 ⟨t, _⟩).2.2, 
   unfold shift_order at h, simp at h, unfold comp_of_path paste fb_path, 
   unfold par_aux_b, rw if_neg, simpa [h], 
   refine not_lt.2 _, simp, exact (par T2._proof_1 ⟨t, _⟩).2.1, 
end

lemma f_inv_comp_at_one {α : Type*} [topological_space α ] {x y : α } (f : path x y) :
∀ (y_1 : I01), f_inv_comp f (1, y_1) = (loop_const y).to_fun y_1 :=
begin  
 intro t, unfold f_inv_comp fa_inv_comp fb_inv_comp repar_stop_a repar_stop_b,  
 unfold paste, unfold shift_order, split_ifs, 
   unfold shift_order at h, simp at h, unfold loop_const, unfold par_aux_a, split_ifs with h₂ , 
     exact f.at_one, 
     simp [not_lt,  -sub_eq_add_neg] at h₂ ,
     have H :  (par T1._proof_1 ⟨t, _⟩).val ≤ 1 - 1,  exact h₂ , rw [sub_self] at H, 
     have h₃ : (par T1._proof_1 ⟨t, h⟩).val = 0, --
        exact le_antisymm H ((par T1._proof_1 ⟨t, h⟩).2.1), 
     have H2 : (par T1._proof_1 ⟨t, h⟩) = (0: I01), 
        exact subtype.eq h₃ , 
     show f.to_fun (par_inv (par T1._proof_1 ⟨t, h⟩)) = y, rw H2, simp, 
   unfold shift_order at h, simp at h, unfold par_aux_b, unfold loop_const, split_ifs with h₂, 
     exact f.at_one, 
     simp [not_lt,  -sub_eq_add_neg] at h₂, 
     have H : (par T2._proof_1 ⟨t, _⟩).val = (1:I01).val, 
       apply eq.symm, exact le_antisymm h₂ (par T2._proof_1 ⟨t, _⟩).2.2, 
     have H2 : (par T2._proof_1 ⟨t, _⟩) = (1: I01), exact subtype.eq H, 
     simp [H2], 
end



lemma f_inv_comp_cont {α : Type*} [topological_space α ] {x y : α } (f : path x y) :
continuous (f_inv_comp f) := 
begin 
  unfold f_inv_comp, refine continuous.comp continuous_shift_order _,  
  refine cont_of_paste prod_T1_is_closed prod_T2_is_closed _ 
    (cont_fa_inv_comp f) (cont_fb_inv_comp f), 
  { unfold match_of_fun, intros w B1 B2, -- can strip out this..? 
    have Int : w ∈ set.inter (set.prod T1 I) (set.prod T2 I), exact ⟨ B1 , B2 ⟩ , rwa [prod_inter_T] at Int, 
    have V : w.1.1 = 1/2, rwa [set.prod, mem_set_of_eq] at Int, rwa [mem_set_of_eq] at Int, exact Int.1, cases w, 
    have xeq : w_fst = ⟨ 1/2 , help_01 ⟩ , apply subtype.eq, rw V, --
    simp [xeq, -one_div_eq_inv], unfold  fa_inv_comp fb_inv_comp, 
    unfold repar_stop_a repar_stop_b shift_order par_aux_a par_aux_b, simp [-sub_eq_add_neg,-one_div_eq_inv], 
    show f.to_fun
      (ite (1 - w_snd.val < (par T1._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T1⟩).val) w_snd
         (par_inv (par T1._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T1⟩))) =
    f.to_fun
      (ite ((par T2._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T2⟩).val < w_snd.val) w_snd
         (par T2._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T2 ⟩)),  
    rw [eqn_1, eqn_2, eqn_2_par_inv], rw sub_lt, 
    show f.to_fun (ite (1 - (1:ℝ ) < w_snd.val) w_snd 0) = 
    f.to_fun (ite ((0:ℝ)  < w_snd.val) w_snd 0), rw sub_self, 
  }, 
end



noncomputable def hom_inv_comp_to_const {α : Type*} [topological_space α ] {x y : α } (f : path x y) : 
path_homotopy (comp_of_path (inv_of_path f) f) (loop_const y) := 
path_homotopy.mk' (f_inv_comp f) (f_inv_comp_start_pt f) (f_inv_comp_end_pt f) 
(f_inv_comp_at_zero f) (f_inv_comp_at_one f) (f_inv_comp_cont f)  


----------------------------------------------------------------------

-- Homotopy of three paths (associativity)
------ (f ⬝ g) ⬝ h ≈ f ⬝ ( g ⬝ h)  



--- Reparametrisation on [1/2, 1]

lemma help_p3_aux₁  (s : T2) : (s.val).val - 1 / 4 ∈ I01 := 
begin 
unfold I01, rw mem_set_of_eq, split, 
 refine  le_sub_iff_add_le.2 _,  rw [add_comm, add_zero], refine le_trans _ s.2.1, norm_num,
 refine le_trans s.2.2 _, norm_num, 
end


lemma help_p3_aux₂  ( s : T2) :  2 * (s.val).val - 1 ∈ I01 := 
begin 
 unfold I01, 
 rw mem_set_of_eq, split, 
  have h₁ : 1/2 ≤ (s.val).val, exact s.2.1, 
  refine le_sub_iff_add_le.2 _, rw [add_comm, add_zero], 
  have H : (2 : ℝ) > 0, norm_num, rw mul_comm, 
  refine (div_le_iff H).1 _, exact h₁, 
  have h₂ : (s.val).val ≤ (1:ℝ ), exact s.2.2, 
  have H2 : 2*(s.val).val ≤ 2 * 1, 
  have HH : 0 < (2 : ℝ), norm_num, 
  refine (@mul_le_mul_left _ _ s.1.1 1 2 HH ).2 _, exact h₂,
  rw [mul_one] at H2, exact H2, 
end


def p3_aux : T2 → I01 := 
λ s, if s.1.1 < (3/4: ℝ ) then ⟨ s.1.1 - 1/4 , help_p3_aux₁ s ⟩  else ⟨ ( 2 : ℝ )*s.1.1 - (1: ℝ) , help_p3_aux₂  s ⟩ 

lemma help_cont_p3_aux₁ : continuous (λ (s : ↥T2), (s.val).val - 1 / 4) := 
continuous.comp  (continuous.comp continuous_subtype_val continuous_subtype_val) (real.continuous_sub_const  (1/4) )

lemma help_cont_p3_aux₂  : continuous (λ (s : ↥T2), 2 * (s.val).val - 1) := 
continuous.comp  (continuous.comp continuous_subtype_val continuous_subtype_val) (real.continuous_linear 2 (-1) )


lemma cont_p3_aux : continuous p3_aux := 
begin 
unfold p3_aux, 
refine continuous_if _ _ _, 
  intros x h, 
 have h₂ := mem_frontier_lt (continuous.comp continuous_subtype_val continuous_subtype_val) (continuous_const) h, 
 simp at h₂ , refine subtype.eq _, norm_num [h₂ ], 
 exact continuous_subtype_mk _ help_cont_p3_aux₁,  
 refine continuous_subtype_mk _ help_cont_p3_aux₂,
end

-----------------------------

-- Reparametrisation on [0, 1/2]

lemma help_p3_T1_aux (x : T1) : 1 / 2 * (x.val).val ∈ I01 :=
begin 
  unfold I01, rw mem_set_of_eq, split, 
   refine mul_nonneg _ x.2.1, {norm_num}, 
   --norm_num [x.2.2], 
   have h :  x.val.val ≤ 1/2 , exact x.2.2, 
   have h₂ : 1 / 2 * (x.val).val ≤ (1/2 : ℝ )* (1/2:ℝ ), have g₁ : (1/ 2 : ℝ)  ≤ 1/2, refine @le_of_eq _ _ (1/2:ℝ ) (1/2:ℝ ) (refl (1/2:ℝ )), 
   refine mul_le_mul g₁ h x.2.1 _ , {norm_num}, 
   refine le_trans h₂ _  ,
   norm_num, 
end

def p3_T1_aux : T1 → I01 := λ x, ⟨ (1/2:ℝ ) * x.1.1 , help_p3_T1_aux x ⟩ 

lemma cont_p3_T1_aux : continuous p3_T1_aux := 
begin 
 unfold p3_T1_aux, 
 refine continuous_subtype_mk _ ( continuous.comp 
  (continuous.comp continuous_subtype_val continuous_subtype_val) (real.continuous_mul_const (1/2)) ) , 
end



noncomputable def p3 : repar_I01 := 
{ to_fun := paste cover_I01 p3_T1_aux p3_aux, 

  at_zero := 
  begin unfold paste, rw dif_pos, unfold p3_T1_aux, dsimp, refine subtype.eq _, 
  exact help_T1, dsimp, exact mul_zero _,  end, 

  at_one := 
  begin unfold paste, rw dif_neg, unfold p3_aux, rw if_neg, refine subtype.eq _, exact help_02, 
  dsimp, show 2 * (1:ℝ) + -1 = 1, {norm_num}, dsimp, rw not_lt, show 3 / 4 ≤ ( 1:ℝ ), norm_num, end, 

  cont := 
  begin 
  refine cont_of_paste T1_is_closed T2_is_closed _ cont_p3_T1_aux cont_p3_aux , 
  unfold match_of_fun,  intros x B1 B2,
    have Int : x ∈ set.inter T1 T2, exact ⟨ B1 , B2 ⟩ , 
    rwa [inter_T] at Int, 
    have V : x.val = 1/2, rwa [mem_set_of_eq] at Int, 
    unfold p3_aux p3_T1_aux, dsimp, rw if_pos, rw subtype.ext , dsimp, norm_num [V], 
  end, 

}

section 
variables {f : path x y} {g : path y z} {h : path z w}

-- To prove associativity need to show the reparametrisation of path 

-- Lemmas for 2

lemma p3_ineq_T1 {t : {x // x ∈ I01}} (h_1 : t ∈ T1 )  : p3.to_fun t ∈ {x : I01 | 0 ≤ x.val ∧ x.val ≤ 1 / 4 } :=
begin 
  rw mem_set_of_eq, split, 
    unfold p3, dsimp, unfold paste p3_T1_aux, simp [h_1, -one_div_eq_inv], refine mul_nonneg _ t.2.1 , {norm_num},
    unfold p3, dsimp, unfold paste p3_T1_aux, simp [h_1, -one_div_eq_inv], 
    have h₂ : (1/4 : ℝ) = (1/2)*(1/2), {norm_num}, rw h₂, unfold T1 T at h_1,  
    have h₃ := h_1.2, 
    refine mul_le_mul _ h₃ t.2.1 _ , exact le_of_eq (refl (1/2)), {norm_num}, 
end 

lemma par_T1_ineq₁ {s : {x // x ∈ I01}} {h_1 : s ∈ T1 } (h : s ∈ {x : ↥I01 | 0 ≤ x.val ∧ x.val ≤ 1 / 4 } ) :
par T1._proof_1 ⟨ s , h_1 ⟩ ∈ T1 := 
begin 
 unfold T1 T, rw mem_set_of_eq, split,
   { unfold par, dsimp [-sub_eq_add_neg], rw sub_zero, rw sub_zero, refine (le_div_iff _ ).2 _, {norm_num}, 
   rw [mul_comm, mul_zero], exact s.2.1, }, 
   unfold par, dsimp [-sub_eq_add_neg], rw sub_zero, rw sub_zero, refine (le_div_iff _ ).1 _ ,{norm_num}, 
   have h₂ : 1 / 2 / (1 / 2)⁻¹ = (1/4 : ℝ ), {norm_num}, rw h₂, 
   exact h.2, 
end

-- Lemmas for 4

lemma p3_not_T1 {t : {x // x ∈ I01}} (h : t ∉  T1 ) :  1/4 < (p3.to_fun t ).val := 
begin  
 have h₁ : 1/2 < t.val, 
  { unfold T1 T at h,
   by_contradiction, rw [not_lt] at a, 
   suffices a₁ : t ∈  {x : ↥I01 | 0 ≤ x.val ∧ x.val ≤ 1 / 2}, cc, 
   exact ⟨ t.2.1, a ⟩ , 
  }, 
  unfold p3, dsimp, unfold paste, simp [h, -one_div_eq_inv], unfold p3_aux, split_ifs, 
  { refine lt_sub_iff_add_lt.2 _, have a₁ : 1 / 4 + 1 / 4 = (1/2:ℝ ), {norm_num}, rw a₁ , exact h₁ },
  simp at h_1, 
  have a₁ : 5 / 4 < 2 * t.val, 
    { have H : 5 / 4 = (5 /3 )*(3/4:ℝ ), {norm_num}, rw H, 
    refine mul_lt_mul _ h_1 _ _, norm_num }, 
  norm_num [a₁ ] , 
end


lemma p3_impl₁ {t : {x // x ∈ I01}} (h : (p3.to_fun t ).val ≤ 1/4 )  : t ∈ T1 :=
begin 
 by_contradiction, 
  have h₂  : 1/4 < (p3.to_fun t ).val, exact p3_not_T1 a, 
  --have g₁ : (1/4:ℝ )< 1/4 , 
  suffices g₁ : ¬  (p3.to_fun t).val ≤ 1 / 4, cc, 
  exact (le_not_le_of_lt h₂).2  , 
end

lemma par_impl_T1  {t : {x // x ∈ I01}} {h_3 : p3.to_fun t ∈ T1} (h_4 : par T1._proof_1 ⟨p3.to_fun t, h_3⟩ ∈ T1) : 
(p3.to_fun t ).val ≤ 1/4 := 
begin 
 unfold par T1 T at h_4, rw mem_set_of_eq at h_4, cases h_4 with h₁ h₂ , simp [-one_div_eq_inv] at h₂, 
 have H :  (0: ℝ )<(1 / 2) , {norm_num}, 
 have H2 :  1 / 4 = (1/2:ℝ )* (1/2), {norm_num}, rw H2, 
 exact (div_le_iff H).1 h₂ ,  
end

-- 1

lemma step_assoc_1 {t : {x // x ∈ I01}} { h_1 : t ∈ T1 } { h_2 : p3.to_fun t ∈ T1} {h_3 : par T1._proof_1 ⟨p3.to_fun t, h_2 ⟩ ∈ T1} : 
f.to_fun (par T1._proof_1 ⟨t, h_1⟩) = f.to_fun (par T1._proof_1 ⟨par T1._proof_1 ⟨p3.to_fun t, h_2⟩, h_3⟩) :=
begin 
 unfold p3, dsimp, 
 unfold paste,  simp [dif_pos, h_1],
 unfold p3_T1_aux, dsimp, 
 unfold par, dsimp, simp [subtype.ext], 
 show  f.to_fun ⟨↑t / 2⁻¹, _⟩ = f.to_fun ⟨((2⁻¹ * t.val )/ 2⁻¹ )/ 2⁻¹, _⟩, 
 have h₁ : ((2⁻¹ * t.val) / 2⁻¹) / 2⁻¹ = ↑t / 2⁻¹, 
  rw mul_div_assoc, 
  show 2⁻¹ * (t.val / 2⁻¹ )/ 2⁻¹ = ↑t / 2⁻¹, 
  have h₂ : 2⁻¹ * (t.val / 2⁻¹) = t.val, refine mul_div_cancel' t.val _ , {norm_num},
  rw h₂ , refl, 
 show  f.to_fun ⟨↑t / 2⁻¹, _⟩ = f.to_fun ⟨((2⁻¹ * t.val )/ 2⁻¹ )/ 2⁻¹, _⟩, 
 simp [h₁] , 
end 

-- 2

lemma help_step_assoc_2 {t : {x // x ∈ I01}} (h_1 : t ∈ T1 ) { h_2 : p3.to_fun t ∈ T1} (h_3 : par T1._proof_1 ⟨p3.to_fun t, h_2⟩ ∉ T1) : 
par T1._proof_1 ⟨p3.to_fun t, h_2⟩ ∈  T2 :=  T2_of_not_T1 h_3 


lemma step_assoc_2 {t : {x // x ∈ I01}} { h_1 : t ∈ T1 } { h_2 : p3.to_fun t ∈ T1} (h_3 : par T1._proof_1 ⟨p3.to_fun t, h_2⟩ ∉ T1) : 
f.to_fun (par T1._proof_1 ⟨t, h_1⟩) = g.to_fun (par T2._proof_1 ⟨par T1._proof_1 ⟨p3.to_fun t, h_2⟩, help_step_assoc_2 h_1 h_3 ⟩) :=
begin 
by_contradiction, unfold T1 T at h_2, 
rw [mem_set_of_eq] at h_2, 
unfold T1 T at h_3, rw [mem_set_of_eq] at h_3, 
simp [-one_div_eq_inv] at h_3, 
have H := h_3 (par T1._proof_1 ⟨p3.to_fun t, h_2⟩).2.1, 
have G : par T1._proof_1 ⟨p3.to_fun t, h_2⟩ ∈ T1, 
exact par_T1_ineq₁ (p3_ineq_T1 h_1), cc, 
end 

--3

lemma step_assoc_3 {t : {x // x ∈ I01}} ( h_1 : t ∈ T1 ) ( h_2 : p3.to_fun t ∉ T1) : 
f.to_fun (par T1._proof_1 ⟨t, h_1⟩) = h.to_fun (par T2._proof_1 ⟨p3.to_fun t, T2_of_not_T1 h_2 ⟩) := 
begin 
by_contradiction, -- as p3.to_fun t ∈ {x : ↥I01 | 0 ≤ x.val ∧ x.val ≤ 1 / 4 } ⊆ T1 
 have h₁ : p3.to_fun t ∈ {x : ↥I01 | 0 ≤ x.val ∧ x.val ≤ 1 / 4 }, exact p3_ineq_T1  h_1, 
 suffices g₁ : p3.to_fun t ∈ T1, cc, 
 refine mem_of_mem_of_subset h₁ _, unfold T1 T, 
 intros x H , refine ⟨ H.1, le_trans H.2 _ ⟩ , {norm_num}
end

--4

lemma step_assoc_4 {t : {x // x ∈ I01}} ( h_1 : t ∉ T1 ) ( h_2 : par T2._proof_1 ⟨t, T2_of_not_T1 h_1 ⟩ ∈ T1) 
( h_3 : p3.to_fun t ∈ T1) (h_4 : par T1._proof_1 ⟨p3.to_fun t, h_3⟩ ∈ T1) : 
 g.to_fun (par T1._proof_1 ⟨par T2._proof_1 ⟨t, _⟩, h_2⟩) =
    f.to_fun (par T1._proof_1 ⟨par T1._proof_1 ⟨p3.to_fun t, h_3⟩, h_4⟩) := 
begin 
by_cases H : t.val = (1/2), 
  { unfold p3, dsimp, unfold paste p3_aux, simp [h_1, -one_div_eq_inv, -sub_eq_add_neg], 
  have h₁ : t.val < 3 / 4, rw H, {norm_num}, simp [h₁, -one_div_eq_inv, -sub_eq_add_neg, H ],  
  have a₁ : 1 / 2 - 1 / 4 = (1/4 : ℝ ), {norm_num}, simp [-one_div_eq_inv, -sub_eq_add_neg, a₁], 
  unfold par, simp [-sub_eq_add_neg, -one_div_eq_inv, sub_zero, H],  
  show g.to_fun ⟨((↑t - 1 / 2) / (1 - 1 / 2)) / (1 / 2), _⟩ = f.to_fun ⟨1 / 4 / (1 / 2) / (1 / 2), _⟩, 
  have a₃  : ↑t = (1/2:ℝ ), exact H, simp [a₃, -one_div_eq_inv  ], simp [div_div_eq_div_mul, -one_div_eq_inv] , 
  norm_num , show g.to_fun 0 = f.to_fun 1,  simp  [ f.at_one, g.at_zero],   }, 

  by_contradiction, 
  suffices G : t ∈ T1, cc, 
  exact p3_impl₁ (par_impl_T1 h_4), 
end  

-- 5

--set_option trace.simplify.rewrite true
--set_option pp.implicit true
lemma p3_image_not_T1 (t : {x // x ∈ I01}) (h_1 : t ∉ T1) (a_1 : 3 / 4 < t.val) : p3.to_fun t ∉  T1 := 
begin 
 unfold T1 T, rw mem_set_of_eq, simp [-one_div_eq_inv], intro H, unfold p3, dsimp, unfold paste p3_aux, 
 simp [h_1, -one_div_eq_inv, -sub_eq_add_neg], 
 have h : ¬ t.val < 3/4, refine not_lt_of_ge (le_of_lt a_1),  simp [h, -one_div_eq_inv, -sub_eq_add_neg], 
 have a₁ : 1 + 1 / 2 = (3/4:ℝ )*2 , {norm_num}, rw mul_comm, 
 simp [-one_div_eq_inv, a₁ ],refine mul_lt_mul a_1 (le_of_eq (refl(2:ℝ ))) _ t.2.1, {norm_num}
end

lemma step_assoc_5  {t : {x // x ∈ I01}} ( h_1 : t ∉ T1 ) ( h_2 : par T2._proof_1 ⟨t, T2_of_not_T1 h_1 ⟩ ∈ T1) 
( h_3 : p3.to_fun t ∈ T1) (h_4 : par T1._proof_1 ⟨p3.to_fun t, h_3⟩ ∉ T1) : 
g.to_fun (par T1._proof_1 ⟨par T2._proof_1 ⟨t, T2_of_not_T1 h_1⟩, h_2⟩) =
    g.to_fun (par T2._proof_1 ⟨par T1._proof_1 ⟨p3.to_fun t, h_3⟩, T2_of_not_T1 h_4 ⟩) := 
begin 
 unfold p3,  dsimp, unfold paste, simp [h_1],  unfold p3_aux,
 by_cases a : t.val = 3/4 , 
  { have a₂ : ¬ t.val < 3/4, exact not_lt_of_ge (ge_of_eq a), simp [a₂], 
   unfold par, dsimp [-one_div_eq_inv, -sub_eq_add_neg],   simp [sub_zero, -one_div_eq_inv, -sub_eq_add_neg],
   have g₁ : (1 - 1 / 2) = (1/2:ℝ ), {norm_num}, simp [g₁, -one_div_eq_inv, -sub_eq_add_neg], 
   have g₂ : ↑t = t.val, trivial, simp [g₂, -one_div_eq_inv, -sub_eq_add_neg] , 
   have g₃ : ((-1 + 2 * t.val) / (1 / 2) - 1 / 2) = (t.val - 1 / 2) / (1 / 2), rw a, {norm_num}, 
   simp [g₃ , -one_div_eq_inv, -sub_eq_add_neg], 
  },
   have l₁ : t.val ≤ 3/4, 
    { by_contradiction, rw not_le at a_1, suffices G : p3.to_fun t ∉  T1, cc, 
     exact p3_image_not_T1 t h_1 a_1, }, 
   have l₂ : t.val < 3 / 4, exact lt_of_le_of_ne l₁ a ,
   simp [l₂ , -one_div_eq_inv, -sub_eq_add_neg], unfold par, dsimp [-one_div_eq_inv, -sub_eq_add_neg],
   simp [-sub_eq_add_neg, -one_div_eq_inv, sub_zero], 
   have g₁ : (1 - 1 / 2) = (1/2:ℝ ), {norm_num}, have g₂ : ↑t = t.val, trivial, 
   simp [g₁ , g₂ , -one_div_eq_inv, -sub_eq_add_neg] ,
   suffices G1 : ((t.val - 1 / 4) / (1 / 2) - 1 / 2) = (t.val - 1 / 2) / (1 / 2), 
     simp [-one_div_eq_inv, -sub_eq_add_neg, G1], 
   show ((t.val - 1 / 4) / (1 / 2)) - (1 / 2) = (t.val - 1 / 2) / (1 / 2), 
   have H1 : (t.val - 1 / 4) / (1 / 2) - (1 / 2) = (t.val - 1 / 4) / (1 / 2) - (1 / 4 ) / (1/2:ℝ ), 
     have h₁ : - (1 / 2 : ℝ ) = - (1 / 4 ) / (1/2:ℝ ), {norm_num}, simp [-one_div_eq_inv, -sub_eq_add_neg, h₁], {norm_num}, 
   rw H1, rw div_sub_div_same, 
   have H2 : (t.val - 1 / 4 - 1 / 4) = (t.val - 1 / 2) , {norm_num}, 
   simp [-one_div_eq_inv, -sub_eq_add_neg, H2], 
end


-- 6 







/- 



α : Type ?,
_inst_3 : topological_space α,
x y z w : α,
f : path x y,
g : path y z,
h : path z w,
t : {x // x ∈ I01},
h_1 : t ∉ T1,
h_2 : par T2._proof_1 ⟨t, _⟩ ∈ T1,
h_3 : p3.to_fun t ∈ T1,
h_4 : par T1._proof_1 ⟨p3.to_fun t, h_3⟩ ∉ T1
⊢ g.to_fun (par T1._proof_1 ⟨par T2._proof_1 ⟨t, _⟩, h_2⟩) =
    g.to_fun (par T2._proof_1 ⟨par T1._proof_1 ⟨p3.to_fun t, h_3⟩, _⟩)

6
α : Type ?,
_inst_3 : topological_space α,
x y z w : α,
f : path x y,
g : path y z,
h : path z w,
t : {x // x ∈ I01},
h_1 : t ∉ T1,
h_2 : par T2._proof_1 ⟨t, _⟩ ∈ T1,
h_3 : p3.to_fun t ∉ T1
⊢ g.to_fun (par T1._proof_1 ⟨par T2._proof_1 ⟨t, _⟩, h_2⟩) = h.to_fun (par T2._proof_1 ⟨p3.to_fun t, _⟩)

α : Type ?,
_inst_3 : topological_space α,
x y z w : α,
f : path x y,
g : path y z,
h : path z w,
t : {x // x ∈ I01},
h_1 : t ∉ T1,
h_2 : par T2._proof_1 ⟨t, _⟩ ∉ T1,
h_3 : p3.to_fun t ∈ T1,
h_4 : par T1._proof_1 ⟨p3.to_fun t, h_3⟩ ∈ T1
⊢ h.to_fun (par T2._proof_1 ⟨par T2._proof_1 ⟨t, _⟩, _⟩) =
    f.to_fun (par T1._proof_1 ⟨par T1._proof_1 ⟨p3.to_fun t, h_3⟩, h_4⟩)

α : Type ?,
_inst_3 : topological_space α,
x y z w : α,
f : path x y,
g : path y z,
h : path z w,
t : {x // x ∈ I01},
h_1 : t ∉ T1,
h_2 : par T2._proof_1 ⟨t, _⟩ ∉ T1,
h_3 : p3.to_fun t ∈ T1,
h_4 : par T1._proof_1 ⟨p3.to_fun t, h_3⟩ ∉ T1
⊢ h.to_fun (par T2._proof_1 ⟨par T2._proof_1 ⟨t, _⟩, _⟩) =
    g.to_fun (par T2._proof_1 ⟨par T1._proof_1 ⟨p3.to_fun t, h_3⟩, _⟩)

α : Type ?,
_inst_3 : topological_space α,
x y z w : α,
f : path x y,
g : path y z,
h : path z w,
t : {x // x ∈ I01},
h_1 : t ∉ T1,
h_2 : par T2._proof_1 ⟨t, _⟩ ∉ T1,
h_3 : p3.to_fun t ∉ T1
⊢ h.to_fun (par T2._proof_1 ⟨par T2._proof_1 ⟨t, _⟩, _⟩) = h.to_fun (par T2._proof_1 ⟨p3.to_fun t, _⟩)

-/







set_option trace.simplify.rewrite true
--set_option pp.implicit true

noncomputable def hom_comp_f_g_h {α : Type*} [topological_space α ] {x y z w : α } ( f : path x y) ( g : path y z) ( h : path z w)  : 
path_homotopy  ( comp_of_path f (comp_of_path g h)) (comp_of_path (comp_of_path f g) h ) := 
begin 
  have h₁ : ( comp_of_path f (comp_of_path g h)) = repar_path (comp_of_path (comp_of_path f g) h )  p3, 
   { unfold repar_path, dsimp, refine path_equal.2 _ ,  dsimp, unfold comp_of_path, dsimp, 
     unfold paste fa_path fb_path fgen_path, dsimp,  unfold paste, funext, unfold paste, 
     split_ifs, 
      exact step_assoc_1,  
      exact step_assoc_2 h_3, 
      exact step_assoc_3 h_1 h_2, 
      exact step_assoc_4 h_1 h_2 h_3 h_4, 
      exact step_assoc_5 h_1 h_2 h_3 h_4, 
      /- 
      { 

        sorry, 
      }
     by_cases H : t ∈ T1, simp [H], 
       { 

sorry
       },
    --refine path_equal.2 _ ,

     sorry -/ sorry, 
   },
rw h₁ , exact hom_repar_path_to_path (comp_of_path (comp_of_path f g) h ) p3, 
end 


/- noncomputable def hom_const_f_to_f {α : Type*} [topological_space α ] {x y : α } ( f : path x y) : path_homotopy (comp_of_path (loop_const x) f ) f:= 
begin 
have H : comp_of_path (loop_const x) f = repar_path f p2, 
  { apply path_equal.2, unfold comp_of_path repar_path, simp, unfold fa_path fb_path fgen_path loop_const p2, simp, unfold par, funext,  
  unfold paste,  split_ifs, simp [-one_div_eq_inv], 
     }, 
rw H, exact hom_repar_path_to_path f p2, 
end -/


/- noncomputable def p2 : repar_I01 := 
{   to_fun :=  λ  t, (paste cover_I01 (λ s, 0 )(λ s, par T2._proof_1 s ) ) t ,  
    at_zero := begin unfold paste, rw dif_pos, exact help_T1,  end, 
    at_one := begin unfold paste, rw dif_neg, exact eqn_end , exact help_02  end, 
    cont := begin simp, refine cont_of_paste _ _ _ continuous_const (continuous_par _), 
        exact T1_is_closed, 
        exact T2_is_closed, 
        unfold match_of_fun,  intros x B1 B2,
        have Int : x ∈ set.inter T1 T2, exact ⟨ B1 , B2 ⟩ , 
        rwa [inter_T] at Int, 
        have V : x.val = 1/2, rwa [mem_set_of_eq] at Int, 
        have xeq : x = (⟨ 1/2 , help_01 ⟩ : I01 ) , apply subtype.eq, rw V, 
        simp [xeq, -one_div_eq_inv], 
        show 0 = par T2._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T2⟩, apply eq.symm, exact eqn_2
    end
}


--mul (id_eq_class x) a = a
noncomputable def hom_const_f_to_f {α : Type*} [topological_space α ] {x y : α } ( f : path x y) : path_homotopy (comp_of_path (loop_const x) f ) f:= 
begin 
have H : comp_of_path (loop_const x) f = repar_path f p2, 
  { apply path_equal.2, unfold comp_of_path repar_path, simp, unfold fa_path fb_path fgen_path loop_const p2, simp, unfold par, funext,  
  unfold paste,  split_ifs, simp [-one_div_eq_inv], 
     }, 
rw H, exact hom_repar_path_to_path f p2, 
end-/















end 


/-  path_homotopy (comp_of_path (comp_of_path (quotient.out F) (quotient.out G)) (quotient.out H))
    (comp_of_path (quotient.out F) (comp_of_path (quotient.out G) (quotient.out H)))  -/

end homotopy