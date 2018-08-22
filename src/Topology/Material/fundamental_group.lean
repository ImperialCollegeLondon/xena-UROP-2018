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
import Topology.Material.homotopy
import Topology.Material.homotopy_results


open set filter lattice classical


---------------------------------------------------
---------------------------------------------------

---- FUNDAMENTAL GROUP


namespace fundamental_group
open homotopy
open path
section
variables {α  : Type*} [topological_space α ] {x : α }


instance setoid_hom_path {α : Type*} [topological_space α] (x : α)  :
setoid (path x x) := setoid.mk is_homotopic_to (is_equivalence)

instance setoid_hom_loop {α : Type*} [topological_space α] (x : α)  :
setoid (loop x) := by unfold loop; apply_instance

def space_π₁  {α : Type*} [topological_space α] (x : α) :=
quotient (fundamental_group.setoid_hom_loop x)

def eq_class {α : Type*} [topological_space α ] {x : α } ( f : loop x ) : space_π₁ x :=
quotient.mk f

--

-- Definition of identity and inverse classes 

def id_eq_class {α : Type*} [topological_space α ] (x : α )  : space_π₁ x := ⟦ loop_const x ⟧ 


lemma inv_eq_class_aux {α : Type*} [topological_space α] {x : α} : 
∀ (a b : path x x),
    a ≈ b → ⟦ inv_of_path a ⟧ = ⟦ inv_of_path b ⟧  := 
begin 
intros a b Hab, 
apply quotient.sound, 
cases Hab, 
existsi _, 
exact path_homotopy_of_inv_path Hab,
end 

def inv_eq_class {α : Type*} [topological_space α ] {x : α } : space_π₁ x → space_π₁ x := 
quotient.lift ( λ f, ⟦ inv_of_path f ⟧ ) inv_eq_class_aux


-- Definition of multiplication on π₁ 

lemma mul_aux {α : Type*} [topological_space α] {x : α} :
∀ (a₁ a₂ b₁ b₂ : loop x), a₁ ≈ b₁ → a₂ ≈ b₂ →
    ⟦comp_of_path a₁ a₂⟧ = ⟦comp_of_path b₁ b₂⟧ :=
begin
  intros a₁ a₂ b₁ b₂ H₁ H₂,
  apply quotient.sound,
  cases H₁ ,
  cases H₂ ,
  existsi _,
  exact path_homotopy_of_comp_path H₁ H₂, 
end

protected noncomputable def mul {α : Type*} [topological_space α] {x : α}  :
space_π₁ x → space_π₁ x → space_π₁ x :=
quotient.lift₂ (λ f g, ⟦comp_of_path f g⟧) mul_aux


-- Interface

instance coe_loop_π₁ : has_coe (loop x) (space_π₁ x) := ⟨eq_class⟩

-- To break down mul proofs and use quotient.sound
lemma quotient.out_eq'  {α : Type*} [topological_space α ] {x : α } ( F : space_π₁ x) 
: F = ⟦ quotient.out F ⟧ := 
begin apply eq.symm, exact quotient.out_eq _, end


---------------------------------------------

local notation `fg_mul` := fundamental_group.mul 

local attribute [instance] classical.prop_decidable 

-----------------------------------------------
-- Identity Elememt 


---- Right identity - mul_one

noncomputable def p1 : repar_I01 := 
{   to_fun :=  λ  t, (paste cover_I01 (λ s, par T1._proof_1 s ) (λ s, 1) ) t ,  
    at_zero := begin unfold paste, rw dif_pos, swap, exact help_T1, simp   end, 
    at_one := begin unfold paste, rw dif_neg, exact help_02 end, 
    cont := begin simp, refine cont_of_paste _ _ _ (continuous_par _) continuous_const, 
        exact T1_is_closed, 
        exact T2_is_closed, 
        unfold match_of_fun,  intros x B1 B2,
        have Int : x ∈ set.inter T1 T2, exact ⟨ B1 , B2 ⟩ , 
        rwa [inter_T] at Int, 
        have V : x.val = 1/2, rwa [mem_set_of_eq] at Int, 
        have xeq : x = (⟨ 1/2 , help_01 ⟩ : I01 ) , apply subtype.eq, rw V, 
        simp [xeq, -one_div_eq_inv], 
        show par T1._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T1⟩  = 1, exact eqn_1, 
    end
}


--mul a (id_eq_class x) = a
noncomputable def hom_f_const_to_f {α : Type*} [topological_space α ] {x y : α } ( f : path x y) : path_homotopy (comp_of_path f (loop_const y)) f:= 
begin 
have H : comp_of_path f (loop_const y) = repar_path f p1, 
  { apply path_equal.2, unfold comp_of_path repar_path, simp, unfold fa_path fb_path fgen_path loop_const p1, simp, unfold par, funext,  
  unfold paste,  split_ifs, simp [-one_div_eq_inv], simp,
     }, 
rw H, exact hom_repar_path_to_path f p1, 
end


-- f ⬝ c ≈ f by using homotopy f → f ⬝ c above -- NOT NEEDED for mul_one
lemma path_const_homeq_path {α : Type*} [topological_space α ] {x y : α } ( f : path x y)  : is_homotopic_to (comp_of_path f (loop_const y)) f := 
begin  unfold is_homotopic_to, refine nonempty.intro (hom_f_const_to_f f), end 


-- Now prove [f]*[c] = [f]
theorem mul_one {α : Type*} [topological_space α ] {x : α } ( F : space_π₁ x) : 
fg_mul F (id_eq_class x) = F := 
begin 
  unfold fundamental_group.mul, unfold id_eq_class eq_class, rw [quotient.out_eq' F], 
  apply quotient.sound, existsi _, 
  exact hom_f_const_to_f (quotient.out F),
end


--------

---- Left identity - one_mul

noncomputable def p2 : repar_I01 := 
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
end


-- Now prove [c]*[f] = [f]
theorem one_mul {α : Type*} [topological_space α ] {x : α } ( F : space_π₁ x) : 
fg_mul (id_eq_class x) F = F := 
begin 
  unfold fundamental_group.mul, unfold id_eq_class eq_class, rw [quotient.out_eq' F], 
  apply quotient.sound, existsi _, 
  exact hom_const_f_to_f (quotient.out F),
end

--------------------------

----------------------------------------------------
-- Inverse Element



theorem mul_left_inv {α : Type*} [topological_space α ] {x : α } (F : space_π₁ x) : fg_mul (inv_eq_class F) F = id_eq_class x := 
begin 
 unfold fundamental_group.mul, unfold id_eq_class eq_class inv_eq_class, rw [quotient.out_eq' F],
 apply quotient.sound, existsi _, exact hom_inv_comp_to_const (quotient.out F)
end


---------------------------------------------------
-- Associativity 


theorem mul_assoc {α : Type*} [topological_space α ] {x : α } (F G H: space_π₁ x) : 
fg_mul (fg_mul F G) H = fg_mul F (fg_mul G H) :=  
begin 
 unfold fundamental_group.mul, rw [quotient.out_eq' F ,quotient.out_eq' G , quotient.out_eq' H], 
 apply quotient.sound, 
  existsi _, exact path_homotopy_inverse (
  hom_comp_f_g_h (quotient.out F) (quotient.out G) (quotient.out H)), 
end


-------------

-- Group π₁ (α  , x)

noncomputable def π₁_group {α : Type*} [topological_space α ] (x : α ) : group ( space_π₁ x) := 
{   mul := fundamental_group.mul ,  
    
    mul_assoc := fundamental_group.mul_assoc, 
    
    one := id_eq_class x , 
    one_mul := fundamental_group.one_mul , 
    mul_one := fundamental_group.mul_one , 

    inv :=  inv_eq_class  ,
    mul_left_inv := fundamental_group.mul_left_inv 

}


end 


----------------------------------------------------------------------


-- Section on π₁ (ℝ , x ) to show ℝ is contractible

section 
variable {x : ℝ }

noncomputable theory 

-- x in {} or ()?
def c : loop x := loop_const x

def C : space_π₁ x := id_eq_class x

lemma trivial_check (x : ℝ ) : C = ⟦@c x⟧ := 
by unfold C id_eq_class c  
 

-- Define homotopy to show that any loop f in ℝ is homotopic to the constant loop c_x (based at x)
def homotopy_real_fun ( f : loop x ) : I01 × I01 → ℝ := 
λ st, (1 - st.1.1) * f.to_fun (st.2) + st.1.1 * f.to_fun (0) 

lemma homotopy_real_start_pt ( f : loop x ) : ∀ (s : I01), homotopy_real_fun f (s, 0) = x :=
begin 
 intro s, unfold homotopy_real_fun, simp [-sub_eq_add_neg , sub_mul, add_sub, add_sub_assoc,  sub_self (s.val * x )], 
end

lemma homotopy_real_end_pt ( f : loop x ) :  ∀ (s : I01), homotopy_real_fun f (s, 1) = x :=
begin 
 intro s, unfold homotopy_real_fun, simp [-sub_eq_add_neg , sub_mul, add_sub, add_sub_assoc,  sub_self (s.val * x )],  
end

lemma homotopy_real_at_zero ( f : loop x ) : ∀ (y : I01), homotopy_real_fun f (0, y) = f.to_fun y  :=
begin 
 intro t, unfold homotopy_real_fun, have a₁ : (0:I01).val = (0:ℝ), trivial, 
 simp [-sub_eq_add_neg , a₁ , sub_zero , zero_mul], 
end

lemma homotopy_real_at_one ( f : loop x ) : ∀ (y : I01), homotopy_real_fun f (1, y) = (@c x ).to_fun y := 
begin 
 intro t, unfold homotopy_real_fun c loop_const, have a₁ : (1:I01).val = (1:ℝ), trivial, 
 simp [a₁], 
end

lemma homotopy_real_cont ( f : loop x ) : continuous (homotopy_real_fun f):= 
begin 
 unfold homotopy_real_fun, refine continuous_add _ _, 
   { refine continuous_mul _ _, 
     { refine continuous_add _ _, exact continuous_const, 
     exact continuous.comp (continuous.comp continuous_fst continuous_subtype_val) (continuous_neg continuous_id), 
     },
     exact continuous.comp continuous_snd f.cont, 
   }, 
   refine continuous_mul _ continuous_const, 
   exact continuous.comp continuous_fst continuous_subtype_val, 
end

--Use the above lemmas to define homotopy with path_homotopy.mk' constructor 

definition homotopy_real ( f : loop x ) : path_homotopy f c  := 
path_homotopy.mk' (homotopy_real_fun f) (homotopy_real_start_pt f) (homotopy_real_end_pt f) 
(homotopy_real_at_zero f) (homotopy_real_at_one f)  (homotopy_real_cont f) 

--------------------------

theorem real_trivial_eq_class (F : space_π₁ x) : F = C := 
begin 
 rw quotient.out_eq' F, rw trivial_check, apply quotient.sound, existsi _, 
 exact homotopy_real (quotient.out F), 
end 



end


--set_option trace.simplify.rewrite true
--set_option pp.implicit true


end fundamental_group