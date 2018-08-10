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
import Topology.Material.homotopy


open set filter lattice classical


---------------------------------------------------
---------------------------------------------------

---- FUNDAMENTAL GROUP


namespace fundamental_group
open homotopy
open path
variables {α  : Type*} [topological_space α ] {x : α }


-- life seems easier if you have both these instances, for some reason
instance setoid_hom_path {α : Type*} [topological_space α] (x : α)  :
setoid (path x x) := setoid.mk is_homotopic_to (is_equivalence x x)

instance setoid_hom_loop {α : Type*} [topological_space α] (x : α)  :
setoid (loop x) := by unfold loop;apply_instance

def space_π_1 {α : Type*} [topological_space α] (x : α) :=
quotient (fundamental_group.setoid_hom_loop x)

def eq_class {α : Type*} [topological_space α ] {x : α } ( f : loop x ) : space_π_1 x :=
quotient.mk f

def id_eq_class {α : Type*} [topological_space α ] (x : α )  : space_π_1 x := eq_class (loop_const x)


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

-- Definition of multiplication on π₁ 
protected noncomputable def mul {α : Type*} [topological_space α] {x : α}  :
space_π_1 x → space_π_1 x → space_π_1 x :=
quotient.lift₂ (λ f g, ⟦comp_of_path f g⟧) mul_aux


----------------------------------------------


-- Identity Elememt 


-- right identity - mul_one

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

local attribute [instance] classical.prop_decidable 

--mul a (id_eq_class x) = a
noncomputable def hom_f_to_f_const {α : Type*} [topological_space α ] {x y : α } ( f : path x y) : path_homotopy (comp_of_path f (loop_const y)) f:= 
begin 
have H : comp_of_path f (loop_const y) = repar_path f p1, 
  { apply path_equal.2, unfold comp_of_path repar_path, simp, unfold fa_path fb_path fgen_path loop_const p1, simp, unfold par, funext,  
  unfold paste,  split_ifs, simp [-one_div_eq_inv], simp,
     }, 
rw H, exact hom_repar_path_to_path f p1, 
end


-- f ⬝ c ≈ f by using homotopy f → f ⬝ c above
lemma path_const_homeq_path {α : Type*} [topological_space α ] {x y : α } ( f : path x y)  : is_homotopic_to (comp_of_path f (loop_const y)) f := 
begin  unfold is_homotopic_to, refine nonempty.intro (hom_f_to_f_const f), end 


---local notation `mul` := fundamental_group.mul 



-- Now prove [f][c] = [f]

theorem mul_one {α : Type*} [topological_space α ] {x : α } ( F : space_π_1 x) : fundamental_group.mul F (id_eq_class x) = F := 
begin 
--unfold mul und_mul eq_class, --have H : F = ⟦ quotient.out _ (setoid_hom x) F ⟧, 
--- Code below does not lead to much progress atm
 /- refine quotient.induction_on _ (setoid_hom x) _ F , 
 have f := @quotient.out (loop x) (setoid_hom x) F , 
 have H : F = @quotient.mk _ (setoid_hom x) f , 
 refine eq.symm _ , refine quotient.out_eq _ (setoid_hom x) F , 


 simp [@quotient.exists_rep (loop x) (setoid_hom x) F], 
apply @quotient.out (loop x) (setoid_hom x) , 

unfold mul und_mul  eq_class, let f := out_loop F , have H : F = eq_class f, unfold eq_class,   -- simp [@quotient.out_eq F, eq.symm], 


--have Hf: f = out_loop F, trivial, subst Hf, -/ 
sorry 
end




--set_option trace.simplify.rewrite true
--set_option pp.implicit true

-----

-- Group π₁ (α  , x)

def π_1_group {α : Type*} [topological_space α ] (x : α ) : group (space_π_1 x) := 
{   mul := mul,  
    
    mul_assoc := begin sorry end, 
    
    
    one := id_eq_class x , 

    one_mul := begin sorry end , 
    mul_one := begin sorry end , 

    inv :=  inv_eq_class  ,
    mul_left_inv :=  begin 
    intro F, simp, 
    sorry end 


}



--------------------- Next things after identity for π_1 group 

-- Inverse 



lemma hom_comp_inv_to_const {α : Type*} [topological_space α ] {x : α } (f : loop x) : path_homotopy (comp_of_path (inv_of_path f) f) (loop_const x) := 
{   to_fun := sorry, 
    path_s := sorry, 
    at_zero := sorry, 
    at_one := sorry, 
    cont := sorry

----- NEED STOP FUNCTION


}

--instance : @topological_semiring I01 (by apply_instance )  := 

lemma comp_inv_eqv_const {α : Type*} [topological_space α ] {x : α } (F : space_π_1 x) : is_homotopic_to (comp_of_path (out_loop (inv_eq_class F)) (out_loop F) ) (loop_const x) := 
begin 
unfold is_homotopic_to, 
sorry,

end 


theorem mul_left_inv {α : Type*} [topological_space α ] {x : α } (F : space_π_1 x) : mul (inv_eq_class F) F = id_eq_class x := 
begin 
unfold mul und_mul, unfold id_eq_class, unfold eq_class, simp [quotient.eq], unfold inv_eq_class out_loop,  unfold has_equiv.equiv, 
--suffices H : is_homotopic_to (comp_of_path (out_loop (inv_eq_class F)) (out_loop F) ) (loop_const x)
sorry, 
end




--- out lemma , 

-- (or define multiplication given loops (mul_1) )



-- Ignore below

/- def space_π_1 {α : Type*} [topological_space α ] {x : α } :=  --: set (hom_eq_class x)
{ h : hom_eq_class ( path x x) } -/ 

/- 
def space_π_1 {α : Type*} [topological_space α ] {x : α } : set (set (path x x)) := 
{ ∀ f : loop3 x,  hom_eq_class ( f)   } -/ 


    

/- {   to_fun := sorry, 
    path_s := sorry, 
    at_zero := sorry, 
    at_one := sorry, 
    cont := sorry-/


--set_option trace.simplify.rewrite true
--set_option pp.implicit true


-- Associativity of homotopy 


-- Homotopy as a class ????

end fundamental_group
