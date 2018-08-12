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
setoid (loop x) := by unfold loop; apply_instance

def space_π₁  {α : Type*} [topological_space α] (x : α) :=
quotient (fundamental_group.setoid_hom_loop x)

def eq_class {α : Type*} [topological_space α ] {x : α } ( f : loop x ) : space_π₁ x :=
quotient.mk f

--

-- Definition of identity and inverse classes 

def id_eq_class {α : Type*} [topological_space α ] (x : α )  : space_π₁ x := ⟦ loop_const x ⟧ 

--def inv_eq_class {α : Type*} [topological_space α ] {x : α } (F : space_π₁  x) : space_π_1 x := eq_class (inv_of_path (out_loop F))

def inv_eq_class' {α : Type*} [topological_space α ] {x : α } ( f : loop x ) : space_π₁  x := eq_class (inv_of_path f)

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

instance : has_one (space_π₁ x) := ⟨ id_eq_class x ⟩ 
---Similarly to Zmod37 should do nstances for identity/inverse elements  ? 

-- To break down mul proofs and use quotient.sound
lemma quotient.out_eq'  {α : Type*} [topological_space α ] {x : α } ( F : space_π₁ x) 
: F = ⟦ quotient.out F ⟧ := 
begin apply eq.symm, exact quotient.out_eq _, end


-----



----------------------------------------------

local notation `fg_mul` := fundamental_group.mul 



-----------------------------------------------
-- Identity Elememt 


-- Right identity - mul_one


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


--------------------------

-- Left identity - one_mul

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

----------------------------------------------------

-- Inverse Element


--set_option trace.simplify.rewrite true
--set_option pp.implicit true

-----

-- Group π₁ (α  , x)

noncomputable def π₁_group {α : Type*} [topological_space α ] (x : α ) : group ( space_π₁ x) := 
{   mul := fundamental_group.mul ,  
    
    mul_assoc := begin sorry end, 
    
    
    one := id_eq_class x , 

    one_mul := fundamental_group.one_mul , 
    mul_one := fundamental_group.mul_one , 

    inv :=  sorry , --inv_eq_class  ,
    mul_left_inv :=  begin 
    intro F, simp, 
    sorry end 


}



--------------------- Next things after identity for π_1 group 
-- Not Compiling 

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
