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
noncomputable theorem path_homotopy_of_comp_path {α } [topological_space α] {x y z : α} { a₁ b₁ : path x y} { a₂  b₂  : path y z} 
( F : path_homotopy a₁ b₁ ) ( G : path_homotopy a₂ b₂ ) : path_homotopy (comp_of_path a₁ a₂) (comp_of_path b₁ b₂) := 
begin 
refine path_homotopy.mk' (f_path_comp F G ) _ _ _ _ _, 
exact f_path_comp_start_pt F G, exact f_path_comp_end_pt F G, 
exact f_path_comp_at_zero F G , exact f_path_comp_at_one F G, 
exact f_path_comp_cont F G, 
end


-----------------------------------------------------





end homotopy