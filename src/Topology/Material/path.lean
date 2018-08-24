/-
Copyright (c) 2018 Luca Gerolla. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luca Gerolla, Mario Carneiro, Kevin Buzzard
Definition of path, loop and basic properties. 
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
import Topology.Material.real_results

universe u

open set filter lattice classical

noncomputable theory 

namespace path


---- PATH and I01 DEFINITION
/- The following definition of path was created by Mario Carneiro -/

variables {α  : Type*} [topological_space α ] 


def I01 := {x : ℝ | 0 ≤ x ∧ x ≤ 1}


instance : topological_space I01 := by unfold I01; apply_instance
instance : has_zero I01 := ⟨⟨0, le_refl _, zero_le_one⟩⟩
instance : has_one I01 := ⟨⟨1, zero_le_one, le_refl _⟩⟩

                                                                                                

structure path {α} [topological_space α] (x y : α) :=
(to_fun : I01 → α)
(at_zero : to_fun 0 = x)
(at_one : to_fun 1 = y)
(cont : continuous to_fun)



instance {α} [topological_space α] (x y : α) : has_coe_to_fun (path x y) := ⟨_, path.to_fun⟩ 



----------

--attribute [class] path 



-- PATH INTERFACE

@[simp]
lemma start_pt_path { x y : α } ( f : path x y ) : f.to_fun 0 = x := f.2

@[simp]
lemma end_pt_path { x y : α } ( f : path x y ) : f.to_fun 1 = y := f.3


-- for later paths homotopy -- checking ending points -- Can Remove 
def equal_of_pts (f g : I01 → α ) : Prop := f 0 = g 0 ∧ f 1 = g 1

def equal_of_pts_path { z w x y : α } ( g1 : path x y ) ( g2 : path z w) : Prop := equal_of_pts g1 g2

def check_pts ( x y : α ) ( g : I01 → α ) := g 0 = x ∧ g 1 = y

def check_pts_of_path ( x y : α ) { z w : α } ( h : path z w ) := check_pts x y h.to_fun
------

-- For equality of path, necessary and sufficient equality of constructor 
theorem path_equal { x y : α } {f  g: path x y} :  f = g  ↔  f.to_fun = g.to_fun  := 
begin split, intro H, rw H, intro H2, cases f, cases g, cc,  end 


-- for later paths homotopy
def is_path ( x y : α ) ( f : I01 → α ) : Prop := f 0 = x ∧ f 1 = y ∧ continuous f 


def to_path { x y : α} ( f : I01 → α ) ( H : is_path x y f) : path x y := 
{  to_fun := f,
   at_zero := H.left,
   at_one := H.right.left,
   cont := H.right.right  
}

--- Can Remove
lemma cont_of_path { z w : α }( g : path z w ) : continuous g.to_fun := g.cont 

--- Can Remove
def fun_of_path {α} [topological_space α ]  { x1 x2 : α  } ( g : path x1 x2 ) : I01 → α   := g.to_fun  

--------------------



--- COMPOSITION OF PATHS

-- Unit interval is closed
lemma is_closed_I01 : is_closed I01 := 
begin exact @is_closed_int_clos 0 1 (by norm_num) end 

-- Define closed subintervals of I01 = [0, 1] 
definition T ( a b : ℝ ) ( Hab : a < b ) : set I01 :=  { x : I01 | a ≤ x.val ∧ x.val ≤ b }  

-- Prove any T r s Hrs is closed in I01
lemma T_is_closed  { r s : ℝ } ( Hrs : r < s )  : is_closed (T r s Hrs) := 
begin 
  let R := {x : ↥I01 | r ≤ x.val }, let L := {x : ↥I01 |  x.val ≤ s } , 
  have C1 : is_closed L, 
    { rw is_closed_induced_iff,
    existsi {x : ℝ | 0 ≤ x ∧ x ≤ (min 1 s)},
    split,
      exact is_closed_inter (is_closed_ge' 0)  (is_closed_le' _),
      apply set.ext,intro x,
      show x.val ≤ s ↔ 0 ≤ x.val ∧ x.val ≤ min 1 s,
      split,
        intro H,
        split,
          exact x.property.1,
          apply le_min,exact x.property.2,assumption,
        intro H,
      exact le_trans H.2 (min_le_right _ _), }, 
  have C2 : is_closed R, 
    {rw is_closed_induced_iff,
    existsi {x : ℝ | (max 0 r) ≤ x ∧ x ≤ 1},
    split, 
      exact is_closed_inter (is_closed_ge' _)  (is_closed_le' 1), 
      apply set.ext, intro x,
      show r ≤ x.val ↔ max 0 r ≤ x.val ∧ x.val ≤ 1, 
      split, 
        intro H, 
        split, 
          exact max_le x.2.1 H, 
          exact x.2.2, 
        intro H, exact (max_le_iff.1 H.1).2,  }, 
  have Int : T r s Hrs = set.inter R L, unfold T set.inter, simp, 
  exact (is_closed_inter C2 C1), 
end 

-- Reparametrisation from T _ _ _ to I01
definition par {r s : ℝ} (Hrs : r < s) : T r s Hrs → I01 :=  
λ x, ⟨ (x.val - r)/(s - r) , 
begin 
  have D1 : 0 < (s - r) , by apply sub_pos.2 Hrs, 
  have D2 : 0 < (s - r)⁻¹, by exact inv_pos D1,   
  have N1 : 0 ≤ ((x.val : ℝ ) - r), 
      by exact sub_nonneg.2 (x.property.1), 
  have N2 : (x.val : ℝ )- r ≤ s - r,
      { have this : -r ≤ -r, trivial, 
      show (x.val : ℝ ) + - r ≤ s + - r,
      exact add_le_add (x.property.2) this,}, 
  split, 
    show 0 ≤ ((x.val : ℝ ) - r) * (s - r)⁻¹, 
      by exact mul_nonneg N1 (le_of_lt D2),  
    have H1 : 0 < (s - r), by exact sub_pos.2 Hrs,
    have H2 : ((x.val : ℝ ) - r) / (s - r) ≤ (s - r) / (s - r),
      by exact @div_le_div_of_le_of_pos _ _ ((x.val : ℝ ) - r) (s - r) (s - r) N2 H1,
    rwa [@div_self _ _ (s - r) (ne.symm ( @ne_of_lt _ _ 0 (s - r) H1) ) ] at H2
end ⟩  



-- Continuity of reparametrisation (later employed in compositions of path/homotopy)
lemma continuous_par {r s : ℝ} (Hrs : r < s) : continuous ( par Hrs ) := 
begin 
  unfold par, apply continuous_subtype_mk,
  show continuous (λ (x :  ↥(T r s Hrs)), ((x.1:ℝ ) - r) / (s - r)),
  show continuous ((λ ( y: ℝ ), (y - r) / (s - r)) ∘ (λ (x : ↥(T r s Hrs)), x.val.val)), 
  have H : continuous (λ (x : ↥(T r s Hrs)), x.val.val), 
    exact continuous.comp continuous_subtype_val continuous_subtype_val , 
  exact continuous.comp H (real.continuous_scale (-r) (s-r)), 
end 



-----------------


-- Define T1 = [0, 1/2] and  T2 = [1/2, 1] 

def T1 : set I01 := T 0 (1/2: ℝ ) ( by norm_num  )

def T2 : set I01 := T (1/2: ℝ ) 1 ( by norm_num  )

lemma T1_is_closed : is_closed T1 := 
begin unfold T1, exact T_is_closed _, end 

lemma T2_is_closed : is_closed T2 := 
begin unfold T2, exact T_is_closed _, end 

lemma help_T1 : (0 : I01) ∈ T 0 (1/2) T1._proof_1 := 
begin unfold T, rw mem_set_of_eq, show 0 ≤ (0:ℝ)  ∧ ( 0:ℝ ) ≤ 1 / 2, norm_num,  end 

lemma help_T2 : (1 : I01) ∈ T (1 / 2) 1 T2._proof_1 := 
begin unfold T, rw mem_set_of_eq, split, show 1/2 ≤ (1:ℝ) , norm_num, show (1:ℝ )≤ 1, norm_num,  end 


lemma help_01 : (1 / 2 :ℝ) ∈ I01 := begin unfold I01, rw mem_set_of_eq, norm_num end

lemma help_02 : (1:I01) ∉ T1 := begin unfold T1 T,rw mem_set_of_eq, show ¬(0 ≤ (1:ℝ ) ∧ (1:ℝ) ≤ 1 / 2) , norm_num,  end 

lemma help_half_T1 : ( ⟨ 1/2, help_01⟩  : I01) ∈ T 0 (1/2) T1._proof_1 := 
begin 
  unfold T, exact set.mem_sep 
    (begin dsimp [has_mem.mem, -one_div_eq_inv], unfold set.mem, norm_num, end ) 
    (begin norm_num end ), 
end 


lemma help_half_T2 : ( ⟨ 1/2, help_01⟩  : I01) ∈ T (1/2) 1 T2._proof_1 := 
begin 
  unfold T, exact set.mem_sep 
    (begin dsimp [has_mem.mem, -one_div_eq_inv], unfold set.mem, norm_num, end ) 
    (begin norm_num end ), 
end 

--- Intersection and covering of T1, T2

lemma inter_T : set.inter T1 T2 = { x : I01 | x.val = 1/2 } := 
begin 
  unfold T1 T2 T set.inter, dsimp [mem_set_of_eq, -one_div_eq_inv], apply set.ext, intro x, split, 
    {rw mem_set_of_eq , rw mem_set_of_eq, simp [-one_div_eq_inv], intros A B C D, 
    have H : x.val < 1 / 2 ∨ x.val = 1/2, by exact lt_or_eq_of_le B, 
    exact le_antisymm  B C, },    
    rw mem_set_of_eq , rw mem_set_of_eq, intro H, rw H, norm_num,
end


lemma cover_I01 : T1 ∪ T2 = set.univ := 
begin 
  unfold univ, unfold has_union.union , unfold T1 T2 T, apply set.ext, intro x,unfold set.union,  simp [mem_set_of_eq , -one_div_eq_inv], 
    split, intro H, simp [has_mem.mem], 
  intro B, simp [has_mem.mem] at B, unfold set.mem at B, 
  have H : 0≤ x.val ∧ x.val ≤ 1, exact x.property, simp [or_iff_not_imp_left, -one_div_eq_inv], 
  intro nL, have H2 : (1 / 2 :ℝ )< x.val, exact nL H.1, exact ⟨ le_of_lt H2, H.2 ⟩ ,
end 

lemma T2_of_not_T1 { s : I01} : (s ∉ T1) → s ∈ T2 := 
begin 
  intro H, have H2 : T1 ∪ T2 = @set.univ I01, exact cover_I01, unfold T1 T2 T at *, simp [-one_div_eq_inv],
  rw mem_set_of_eq at H, rw not_and at H, have H3 : 1/2 < s.val, have H4 : ¬s.val ≤ 1 / 2, exact  H (s.2.1), exact lt_of_not_ge H4,
  exact ⟨ le_of_lt H3, s.2.2⟩ , 
end

---- Lemmas to simplify evaluations of par 
@[simp]
lemma eqn_start : par T1._proof_1 ⟨0, help_T1⟩ = 0 := 
begin unfold par, simp [-one_div_eq_inv], exact subtype.mk_eq_mk.2 (begin exact zero_div _,  end  ), end  

@[simp]
lemma eqn_1 : par T1._proof_1 ⟨⟨1 / 2, begin unfold I01, rw mem_set_of_eq, norm_num end⟩, begin unfold T, rw mem_set_of_eq, show 0 ≤ (1/2 : ℝ ) ∧ (1/2 : ℝ ) ≤ 1 / 2 ,  norm_num end ⟩ 
= 1 :=  begin unfold par, simp [-one_div_eq_inv], exact subtype.mk_eq_mk.2 (begin exact div_self (begin norm_num, end), end) end 

@[simp]
lemma eqn_2 : par T2._proof_1 ⟨⟨1 / 2, help_01  ⟩, begin unfold T, rw mem_set_of_eq, show 1/2 ≤ (1/2 : ℝ ) ∧ (1/2 : ℝ ) ≤ 1  ,  norm_num end⟩ 
= 0 := begin unfold par, simp [-one_div_eq_inv], exact subtype.mk_eq_mk.2 (by refl) end 

@[simp]
lemma eqn_end : par T2._proof_1 ⟨1, help_T2 ⟩ = 1 :=  
begin unfold par, exact subtype.mk_eq_mk.2 ( begin show ( ( 1:ℝ ) - 1 / 2) / (1 - 1 / 2) = 1,  norm_num, end ),  end 

-------------------------------------

-- Definition and continuity of general / T1 / T2 reparametrisation of path function (path.to_fun)
---------- to be used with cont_of_paste for path/homotopy composition 

def fgen_path { x y : α } {r s : ℝ} (Hrs : r < s) (f : path x y ) : T r s Hrs → α := 
λ t, f.to_fun ( par Hrs t)

lemma pp_cont { x y : α }{r s : ℝ} (Hrs : r < s)(f : path x y ) : continuous (fgen_path Hrs f) := 
begin unfold fgen_path, exact continuous.comp (continuous_par Hrs) f.cont, end 

definition fa_path { x y : α } (f : path x y ) : T1 → α := λ t, f.to_fun (par T1._proof_1 t)

lemma CA { x y : α } (f : path x y ) : continuous ( fa_path f):= 
begin unfold fa_path, exact continuous.comp (continuous_par T1._proof_1 ) f.cont, end 

definition fb_path { x y : α }(f : path x y ) : T2 → α := λ t, f.to_fun (par T2._proof_1  t)

lemma CB { x y : α } (f : path x y ) :  continuous ( fb_path f):= 
begin unfold fb_path, exact continuous.comp (continuous_par T2._proof_1 ) f.cont, 
end 

----- Composition of Path function 

definition comp_of_path  { x y z : α } ( f : path x y )( g : path y z ) : path x z :=  
{   to_fun := λ t, ( paste  cover_I01 ( fa_path f ) ( fb_path g ) ) t ,  

    at_zero := 
    begin unfold paste, rw dif_pos, unfold fa_path, rw eqn_start, exact f.at_zero end, 

    at_one := 
    begin unfold paste, rw dif_neg, unfold fb_path, 
      show g.to_fun (par T2._proof_1 ⟨1,  help_T2 ⟩) = z, by simp [eqn_end],  
      exact help_02, 
    end,
    
    cont := 
    begin 
    -- both images are f.to_fun 1 = g.to_fun 0 = y 
      have HM :  match_of_fun (fa_path f) (fb_path g),  
        unfold match_of_fun,  intros x B1 B2,
        have Int : x ∈ set.inter T1 T2, exact ⟨ B1 , B2 ⟩ , 
        rwa [inter_T] at Int, 
        have V : x.val = 1/2, rwa [mem_set_of_eq] at Int, 
        have xeq : x = (⟨ 1/2 , help_01 ⟩ : I01 ) , apply subtype.eq, rw V, 
        unfold fa_path fb_path, simp [xeq, -one_div_eq_inv], 
        show f.to_fun (par T1._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T1⟩) = g.to_fun (par T2._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T2⟩),
        simp [eqn_1, eqn_2, -one_div_eq_inv], 
      -- Use pasting lemma via closed T1, T2    
      exact cont_of_paste T1_is_closed T2_is_closed HM (CA f) (CB g),  
    end
}

----------------------------------------------------

--- INVERSE OF PATH

--- Similarly to Composition of Path: define par_inv, prove continuity and create some [simp] lemmas

lemma inv_in_I01 (x : I01) : 1 - x.val ∈ I01 := 
begin unfold I01, rw mem_set_of_eq, split, simp [-sub_eq_add_neg] , exact x.2.2, simp, exact x.2.1, end   

definition par_inv : I01 → I01 :=  λ x, ⟨ 1 - x.val , inv_in_I01 x ⟩ 

@[simp] lemma eqn_1_par_inv : par_inv 0 = 1 :=  by refl

@[simp] lemma eqn_2_par_inv : par_inv 1 = 0 := by refl 


lemma help_inv (y : ℝ ) : ( 1 - y) = (-1) * y + 1 := by simp 

theorem continuous_par_inv : continuous (par_inv ) := 
begin 
  unfold par_inv, apply continuous_subtype_mk,
  show continuous ((λ ( y: ℝ ), 1 - y ) ∘ (λ (x : ↥I01), x.val)), 
  refine continuous.comp continuous_subtype_val _, --
  conv in ( (1:ℝ)-_) 
    begin 
    rw help_inv,
    end , 
  exact continuous.comp (real.continuous_mul_const (-1) ) (real.continuous_add_const 1), 
end


definition inv_of_path { x y : α } ( f : path x y ) : path y x :=  
{   to_fun := λ t , f.to_fun ( par_inv t ) , --  or better f.to_fun ∘ par_inv

    at_zero := begin rw eqn_1_par_inv, exact f.at_one end , 
   
    at_one := begin rw eqn_2_par_inv, exact f.at_zero end, 

    cont := by exact continuous.comp continuous_par_inv f.cont 

}

------------------------------------

-- LOOP 

-- function to check loop (can be removed)
def is_loop { x y : α } ( g : path x y) : Prop := x = y 


def loop (x0 : α) : Type* := path x0 x0 


def loop_const (x0 : α) : loop x0 := 
{   to_fun:= λ t, x0 ,  
    at_zero :=  by refl , 
    at_one := by refl, 
    cont := continuous_const   
} 


end path 