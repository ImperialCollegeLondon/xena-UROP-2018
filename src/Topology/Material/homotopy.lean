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
variables {β  : Type*} [topological_space β ] ( x y : β  )
variables ( z w x0 : β  )
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


variables (f : path x y) (g : path x y)
variable F : path_homotopy f g 

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

def path_homotopy_inverse { x y : β} (f : path x y) (g : path x y) ( F : path_homotopy f g) : path_homotopy g f := 
{   to_fun :=   λ st  , F.to_fun ( par_inv st.1 , st.2 ),
    path_s := begin 
    intro s, unfold is_path, split, 
        exact (F.path_s (par_inv s)).1, split, 
          exact (F.path_s (par_inv s)).2.1, 
            exact (F.path_s (par_inv s)).2.2
    end,  
    at_zero := begin intro t, simp,   end, --exact F.at_one t
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
    cases H with F, exact ⟨path_homotopy_inverse f g F⟩,
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

-----------------------------------------------------


--- Closure result (that I have not found in topological_structures)


@[simp] lemma closure_lt_eq { α β } [topological_space α] [topological_space β] [partial_order α] [t : ordered_topology α]
{f g : β → α} (hf : continuous f) (hg : continuous g) :
  closure {b | f b < g b} = {b | f b ≤ g b} :=
begin 
refine set.eq_of_subset_of_subset _ _, 
refine closure_minimal _ _ , 
 simp, intros a h₁, exact le_of_lt h₁ , 
 exact is_closed_le hf hg, 
sorry
/-
have h₂ : {b : β | f b ≤ g b} = closure {b : β | f b ≤ g b}, sorry, 
rw h₂, 
have h₃ : closure {b : β | f b < g b} = closure ( closure {b : β | f b < g b} ), sorry, 
rw h₃, 
refine closure_mono _  ,

refine closure_su , -/
--refine closure_mono , 
end
















------------------------------------------

-- Homotopy of composition with inverse 
------ a⁻¹ ⬝ a ≈ c₀  

set_option trace.simplify.rewrite true
--set_option pp.implicit true


-- To shrink path f⁻¹ 

/- 
noncomputable def paste {X Y} {A B : set X} (Hunion : A ∪ B = set.univ) (fa : A → Y) (fb : B → Y) (t : X) : Y :=
if h₁ : t ∈ A then fa ⟨t, h₁⟩ else 
have t ∈ A ∪ B, from set.eq_univ_iff_forall.1 Hunion t,
have h₂ : t ∈ B, from this.resolve_left h₁,
fb ⟨t, h₂⟩ -/



def par_aux_a : I01 × I01 → I01 := 
λ st, if ((1 : ℝ ) - st.1.1) < st.2.1 then st.1 else par_inv st.2

-- dite or ite? 

/- if h₁ : ((1 : ℝ ) - st.1.1) ≤ st.2.1 then st.1 else st.2
begin 
have H : st.2.1 < ((1 : ℝ ) - st.1.1), exact not_le.1 h₁ , exact st.2,
end -/ 



lemma continuous_par_aux_a  : continuous par_aux_a := 
begin 
unfold par_aux_a, 
by_cases h : ∀ (st : I01 × I01), ((1 : ℝ ) - ((st.1).1 )) < (st.snd).val , 
simp [h, continuous_fst], 

rw [not_forall] at h, --rw if_neg, 
cases h with x h₂ ,  simp [h₂ , if_neg, continuous_snd], 

 -- does not finish off
/- 
 simp [h, if_false ],   
let x := λ (y : I01 × I01) ,  ¬1 - (y.fst).val ≤ (y.snd).val, 

have h₂ : ¬1 - (x.fst).val ≤ (st.snd).val , 


have h₂ : ∃ (st : ↥I01 × ↥I01), ¬ 1 - (st.fst).val ≤ (st.snd).val, 
  exact not_forall.1 h, -/

/-           have H3:  s ∉ T1, simp [not_forall] at H, exact H.2,
          simp [H3], refine (G.path_s (par T2._proof_1 ⟨ s, _ ⟩  )).2.2,        
          exact T2_of_not_T1 H3, -/

--split_ifs, 
sorry
end

lemma continuous_par_aux_a'  : continuous par_aux_a := 
begin 
unfold par_aux_a, 
refine continuous_if _ continuous_fst _ , 
  { intros st F, 
    have H : frontier {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val} = {a : ↥I01 × ↥I01 | (a.snd).val = 1 - (a.fst).val }, 
        { unfold frontier , 
        have H2 : interior {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val} = {a : ↥I01 × ↥I01 | 1 - (a.fst).val < (a.snd).val}, 
          refine interior_eq_iff_open.2 _, refine is_open_lt  _ _,  
          have h : continuous ( λ (r : ℝ ), 1 - r ), sorry, 
          exact continuous.comp (continuous.comp continuous_fst continuous_subtype_val) h, 
          exact continuous.comp continuous_snd continuous_subtype_val, 
          --refine continuous.comp  continuous_par_inv, 
          rw H2, --rw closed
        
        
        sorry}, 
    rw [H, mem_set_of_eq] at F, unfold par_inv, refine subtype.eq _, 
    show (st.fst).val = 1 -(st.snd).val, simp [F], 
  }, 
exact continuous.comp continuous_snd continuous_par_inv, 
end

#check trunc





/- def par_stop_a : I01 × I01 → I01 := 
λ st, ps_aux_a st -/ 

/- lemma continuous_par_stop_a : continuous par_stop_a := 
begin unfold par_stop_a, exact continuous.prod_mk continuous_fst continuous_ps_aux_a end -/ 

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


#print tendsto
----- 

-- To shrink path f 
def par_aux_b : I01 × I01 → I01 := 
λ st, if st.2.1 < st.1.1 then st.1 else st.2

lemma continuous_par_aux_b  : continuous par_aux_b := 
begin 
unfold par_aux_b, assume U H, 
by_cases h : ∀  (st : I01 × I01), (st.snd).val < (st.fst).val , 
simp [h, continuous_fst], sorry,

rw [not_forall] at h, 
cases h with x h₂ , simp [h₂ , if_neg , continuous_snd], 
sorry
end



lemma continuous_par_aux_b'  : continuous par_aux_b := 
begin 
unfold par_aux_b, 
refine continuous_if _ _ _ , 
 { --rw frontier_eq_closure_inter_closure , rw has_neg.neg , 
     
  intros st F, 
  have H : frontier {a : ↥I01 × ↥I01 | (a.snd).val < (a.fst).val} = {a : ↥I01 × ↥I01 | (a.fst).val = (a.snd).val}, 
    {unfold frontier , 
        have H2 : interior {a : ↥I01 × ↥I01 | (a.snd).val < (a.fst).val} = {a : ↥I01 × ↥I01 | (a.snd).val < (a.fst).val}, 
          refine interior_eq_iff_open.2 _, refine is_open_lt _ _, 
          exact continuous.comp continuous_snd continuous_subtype_val, 
          exact continuous.comp continuous_fst continuous_subtype_val, 
        rw H2,
        have H3 : closure {a : ↥I01 × ↥I01 | (a.snd).val < (a.fst).val} = {a : ↥I01 × ↥I01 | (a.snd).val ≤  (a.fst).val}, 
          {  refine closure_lt_eq _ _, 
              
              
              sorry
          
          }, 
        rw H3, unfold has_sdiff.sdiff set.diff, simp, -- [le_antisymm], 
          apply set.ext, intro x, split, simp , intros a b, exact le_antisymm  b a,
          simp, intro a, refine ⟨ _, le_of_eq a⟩, exact ge_of_eq a, 
    }      , 
  rw H at F, rw mem_set_of_eq at F, exact subtype.eq F,


  --rw frontier_eq_closure_inter_closure at F, 
 --unfold frontier at F, unfold closure at F, unfold interior at F,  rw mem_set_of_eq at F, 
 --rw [ not_le_of_lt  ] at F,  

 }, 
exact continuous_fst, 
exact continuous_snd, 
end

--#print has_sdiff.sdiff


/- def par_stop_b : I01 × I01 → I01 × I01 := 
λ st, (st.1, ps_aux_b st )

lemma continuous_par_stop_b : continuous par_stop_b := 
begin unfold par_stop_b, exact continuous.prod_mk continuous_fst continuous_ps_aux_b end -/ 

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

--------------
/- 
#check le_add_of_le_of_nonneg
#check le_antisymm
#check lt_iff_le_and_ne 
#check lt_of_le_of_lt
#check sub_lt
#check subtype.ext -/

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

#check lt_iff_le_and_ne

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


/- refine continuous.comp continuous_shift_order _,     
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
    exact continuous.comp cont_r_shift_b G.cont, -/

noncomputable def hom_inv_comp_to_const {α : Type*} [topological_space α ] {x y : α } (f : path x y) : 
path_homotopy (comp_of_path (inv_of_path f) f) (loop_const y) := 
path_homotopy.mk' (f_inv_comp f) (f_inv_comp_start_pt f) (f_inv_comp_end_pt f) 
(f_inv_comp_at_zero f) (f_inv_comp_at_one f) (f_inv_comp_cont f)  







--noncomputable def hom_inv_comp_to_const {α : Type*} [topological_space α ] {x y : α } (f : path x y) : path_homotopy (comp_of_path (inv_of_path f) f) (loop_const y) := sorry 

/- constant st : I01 × I01
#check st.2 -/ 


end homotopy