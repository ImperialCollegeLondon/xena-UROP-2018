import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space
import analysis.real
import data.real.basic tactic.norm_num
import data.set.basic

universe u

open set filter lattice classical

noncomputable theory 

section Mario

variables {α  : Type*} [topological_space α ] ( x y : α )

---- 
/- The following definition of path was created by Mario Carneiro -/


def I01 := {x : ℝ // 0 ≤ x ∧ x ≤ 1}

#check I01 

#check topological_space
-- noncomputable def h : ℝ := 0.5 

-- Has euclidean subspace topology/computability?? 
instance : topological_space I01 := by unfold I01; apply_instance
instance : has_zero I01 := ⟨⟨0, le_refl _, zero_le_one⟩⟩
instance : has_one I01 := ⟨⟨1, zero_le_one, le_refl _⟩⟩
/- instance : ( h : I01 ) := begin   
end -/
 
#check has_one 

structure path {α} [topological_space α] (x y : α) :=
(to_fun : I01 → α)
(at_zero : to_fun 0 = x)
(at_one : to_fun 1 = y)
(cont : continuous to_fun)

#print prefix path

/- 
def p : path x y := {
    to_fun := sorry,
    at_zero := sorry,
    at_one := sorry,
   cont := sorry 
 } -/

/- instance {α} [topological_space α] (x y : α) : 
has_coe_to_fun (path x y) := begin exact ⟨_, path.to_fun⟩,
end -/ 

instance {α} [topological_space α] (x y : α) : 
has_coe_to_fun (path x y) := ⟨_, path.to_fun⟩ 



#print prefix path
#check @has_coe_to_fun

end Mario

----------

-- attribute [class] path 



section Interface_One -- Path interface and Loop
variables {α  : Type*} [topological_space α ] ( x y : α )
variables ( z w x0 : α )
variables ( g1 : path x y ) ( g2 : path z w)
variable l : I01 → α 


-- PATH Interface

-- if equal .to_fun (to distinguish loop / continuously deformed)
-- equality of path, starting points and continuity


-- for later paths homotopy -- checking ending points  
def equal_of_pts (f g : I01 → α ) : Prop := f 0 = g 0 ∧ f 1 = g 1

def equal_of_pts_path : Prop := equal_of_pts g1.to_fun g2.to_fun

def check_pts ( x y : α ) ( g : I01 → α ) := g 0 = x ∧ g 1 = y

def check_pts_of_path ( x y : α ) ( h : path z w ) := check_pts x y h.to_fun


def equal_of_path  : Prop := g1.to_fun == g2.to_fun  -- == ? 

/- path.mk : Π {α : Type u_2} [_inst_2 : topological_space α] {x y : α} (to_fun : I01 → α),
  to_fun 0 = x → to_fun 1 = y → continuous to_fun → path x y -/

def is_path ( x y : α ) ( f : I01 → α ) : Prop := f 0 = x ∧ f 1 = y ∧ continuous f 
-- f is to_fun creator 

-- #check is_path x y l 

def to_path { x y : α} ( f : I01 → α ) ( H : is_path x y f) : path x y := 
 {  to_fun := f,
    at_zero := H.left,
    at_one := H.right.left,
    cont := H.right.right  }

lemma cont_of_path ( g : path z w ) : continuous g.to_fun := g.cont 
-- 'Exists' is not a class
#check g1.to_fun 

def fun_of_path {α} [topological_space α ]  { x1 x2 : α  } ( g : path x1 x2 ) : I01 → α    := g.to_fun  
#check fun_of_path g1 -- can write equal_of_path in terms of this 

---------------- 


-- TRIAL

-- import Prof Buzzard subsets 
/- 
theorem pasting_two_closed {α  : Type*} {β   : Type*} [X : topological_space α ] [ topological_space β ]( f : α → β ) 
( U : set α ) ( V : set α ) ( H :  U ∪ V = univ  )  { HU : is_closed U } { HV : is_closed V }
{ ImU : (∀ (a : α), U a → univ (f a))} { ImV : (∀ (a : α), V a → univ (f a))}
( CU :  continuous  ((@subtype.map _ _  U _ f ) ImU ) ) ( CV :  continuous  ((@subtype.map _ _  V _ f ) ImV ) ) 
: continuous f := begin sorry end  -/ 

-- REPARAMATERISATION of PATHS 
/-  1 cts fun [0,1] to [a, b] 
    2 special path maker  $$ evaluating 2*1/2 -/  

 





--- COMPOSITION OF PATHS


noncomputable def h : I01 := ⟨ 1/2,  by norm_num ⟩ 
lemma geq_half : (0 : ℝ) ≤ (1/2 : ℝ) := by norm_num
lemma leq_half : (1/2 : ℝ) ≤ (1 : ℝ) := by norm_num

lemma help_1 : 2 * ( 1 : ℝ ) - 1 = 1 := begin norm_num end  

lemma geq_zero ( t : I01) : t.val ≥ (0:ℝ) := begin dunfold I01 at t, 
sorry   
end 
lemma leq_one ( t : I01) : t.val ≤  (1:ℝ) := begin dunfold I01 at t, sorry end 


--- definition of to_fun in terms of restrictions 
noncomputable def comp_of_path2 {α} [topological_space α] { x y z : α } ( f : path x y )( g : path y z ) : path x z := 
{   to_fun := sorry, 
    at_zero := sorry, 
    at_one := sorry,
    cont := sorry 
}


noncomputable def comp_of_path {α} [topological_space α] { x y z : α } ( f : path x y )( g : path y z ) : path x z :=
{  to_fun := λ t : I01, if H : t.val ≤ 1/2 ∧ t.val ≥ 0 then f.to_fun ⟨(2 : real)*t.val, begin 
    have H2: t.val ≥ (0 : real), 
        exact H.right,  
    have nn2: (2:real) ≥ 0, 
        by norm_num, 
    have pos2: (2:real) > 0, 
        by norm_num, 
    split, 
    exact ( mul_nonneg nn2 H2), 
    have P:  t.val * 2 ≤ 1,
    exact mul_le_of_le_div pos2 H.left, 
    rwa mul_comm at P,        
    end⟩ 
    ----------
else g.to_fun ⟨ (2:real)*t.val - 1 , begin 
    rw not_and_distrib at H,  
    have H2: t.val ≥ 0, 
        exact geq_zero t, 
    have HH : ¬t.val ≤ 1 / 2, 
        have HF : ( ¬t.val ≥ 0 ) = false , simp *, 
        --exact or_eq_of_eq_false_right HF, 
        sorry, 
        --show H :
        --apply or_eq_of_eq_false_right HF at H, 
    --exact or_eq_of_eq_false_right ⟨ H, H2⟩, 
    --rw H with or_eq_of_eq_false_right (⟨ H.right, H2⟩)  ,  
    split, rwa not_le at HH, norm_num, 
        --show (1:ℝ ) ≤ (2:ℝ )*t.val ,   --show HH : ¬t.val  1 / 2
        show 0 ≤ -1 + 2 * (t.val : ℝ ), 
        --show 1 + 0 ≤ 1 +  -1 + 2 * (t.val : ℝ ),
    sorry, 
    have  TL : t.val ≤ 1, exact leq_one t, 
    sorry 
    end ⟩,  
    ---------
    at_zero := begin 
    rw dif_pos, 
        have H : 2*(0 : I01).val = 0, 
            exact mul_zero 2, --show 2 * (0 : ℝ) = 0,
        have H2 : (⟨2*(0:I01).val,_⟩ : I01) = ⟨0,_⟩,tactic.swap,
        rw H2, exact f.at_zero, 
        exact subtype.eq H, split, 
            exact geq_half, 
            show (0:ℝ) ≥ 0, norm_num
        --swap, by norm_num, 
        
        --exact f.at_zero,  -- exact f.at_zero, 
    end ,
    at_one := begin 
    rw dif_neg, 
        have H : 2*(1 : I01).val - 1 = 1, 
            show 2 * ( 1 : ℝ ) - 1 = 1, exact help_1, 
            -- show 1 = 2 * ( 1 : ℝ ) - 1, 
                --norm_num, 
        have H2 : (⟨2 * (1:I01).val - 1, _⟩ : I01) = ⟨1,_⟩, 
            tactic.swap, 
        rw H2, exact g.at_one, 
        exact subtype.eq H,
        show ¬((1 : ℝ) ≤ 1/2 ∧ (1:ℝ ) ≥ 0), rw not_and_distrib ,
            have F: ¬1 ≤ 1 / 2, norm_num
        end ,
    cont := begin unfold continuous,  --rw dif_neg,   
    intro s, intro Hs, 
    -- cases 
    -- have H1: continuous (λ (t : I01), f.to_fun ⟨2 * t.val, _⟩ ) , 
    have Hf: is_open ((λ (t : I01), f.to_fun ⟨2 * t.val, _⟩ ) ⁻¹' s) , 
    --have Hg: is_open ((λ (t : I01),  g.to_fun ⟨2 * t.val - 1, _⟩)) ⁻¹' s) , 

    -- Need cases 
    sorry, sorry, sorry, 
    end -- Pasting lemma

}

-- use path from ℝ 

---
#print prefix dif_ctx_congr
#check mul_le_of_le_div
#check add_eq_of_eq_add_neg
#print prefix real.nonneg 
#check not_and_distrib.1
/- noncomputable def h : I01 :=  1 / 2 

lemma geq_half : (0 : ℝ) ≤ (1/2 : ℝ) := by norm_num
lemma leq_half : (1/2 : ℝ) ≤ (1 : ℝ) := by norm_num

lemma geq_half2 : (0 : I01) ≤ (1/2 : I01) := by norm_num
lemma leq_half2 : (1/2 : I01) ≤ (1 : I01) := by norm_num

instance : ( h : I01 ) := ⟨⟨0, le_refl _, zero_le_one⟩⟩ -/



-- LOOP 

-- Definition of loop -- (extend path??) !!!!
------------

/- 
structure loop {α} [topological_space α] (x : α) { y : α } extends  path x y  := 
(base_pt : to_fun 0 = x ∧ to_fun 1 = x) -/ 

/- structure loop {α} [topological_space α] (x : α) :=
(to_fun : I01 → α)
(base_pt : to_fun 0 = x ∧ to_fun 1 = x)
(cont : continuous to_fun)
-/


def is_loop ( g : path x y) : Prop := g.at_zero == g.at_one -- function to check loop


structure loop {α} [topological_space α] (x : α) extends path x x := 
(base_pt : to_fun 0 = x ∧ to_fun 1 = x) 
--(base_pt : is_loop )

def loop3 {α} [topological_space α] (x0 : α) : Type* := path x0 x0 

--#check loop    --- not quite 
#check @loop
#check @loop3   
#check @path  

-- lemma 
lemma loop_is_path (l1 : loop x0) : path x0 x0  := l1.to_path 



end Interface_One


----------------------------


namespace homotopy -- Homotopy

variables {α  : Type*} [topological_space α ] 
variables {β  : Type*} [topological_space β ] ( x y : β  )
variables ( z w x0 : β  )
variable s : I01 
--variables ( f : path x y ) ( g : path z w)
-- variable h : α → β 


def P := topological_space (I01 × α )

-- HOMOTOPY 

-- General Homotopy 
structure homotopy {α} {β} [topological_space α] [topological_space β] (f : α → β)
( hcf : continuous f) (g : α → β)
( hcg : continuous g) :=
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

#check @path_homotopy  
variables (f : path x y) (g : path x y)
variable F : path_homotopy f g 

#check f.to_fun 0 
#check F.at_zero 
#print prefix path_homotopy 



def hom_to_path { x y : β } { f g : path x y } 
( F : path_homotopy f g ) (s : I01) : path x y := 
to_path ( λ t,  F.to_fun (s, t)) (F.path_s s) 
 

#check (F.path_s s ).left 

-- Ending points of path_homotopy are fixed 
lemma hom_eq_of_pts { x y : β } { f g : path x y } ( F : path_homotopy f g ) : 
∀ s : I01, check_pts x y ( λ t,  F.to_fun (s, t)) := 
-- equal_of_pts f.to_fun ( λ t, F.to_fun (s, t) ) := 
begin 
    intro s, unfold check_pts, split, 
        have H1: F.to_fun (s, 0) =  ( λ t,  F.to_fun (s, t)) 0,
            simp, 
        rw H1, exact (F.path_s s).left,
        have H1: F.to_fun (s, 1) =  ( λ t,  F.to_fun (s, t)) 1,
            simp, 
        rw H1, exact (F.path_s s).right.left 
end 

lemma hom_path_is_cont { x y : β } { f g : path x y } ( F : path_homotopy f g ) : 
∀ s : I01, continuous ( λ t,  F.to_fun (s, t)) := 
begin 
intro s, exact (F.path_s s).right.right 
end 

definition is_homotopic_to { x y : β } (f : path x y) ( g : path x y) : Prop := nonempty ( path_homotopy f g) 


-- Equivalence of Homotopy 
def path_homotopy_id { x y : β} (f : path x y) : path_homotopy f f := 
{   to_fun :=  λ pair  , f.to_fun pair.2 ,  
    path_s := begin  intro s, unfold is_path, 
    exact ⟨ f.at_zero,  f.at_one, f.cont ⟩ end, 
    at_zero := by simp , 
    at_one := by simp ,  
    cont := begin unfold continuous, intro U,  sorry 
    /-
    --have H1 :  ((λ (pair : I01 × I01), f.to_fun (pair.snd)) ⁻¹' U ) =  ( (univ : I01) × (f.to_fun ⁻¹' U) ), -- f.to_fun ⁻¹' U ,
    let I : set I01 := univ, 
    have H3 : is_open (f.to_fun ⁻¹' U), 
        exact ⟨ U, (unfold f.cont) U ⟩

    --have H2: ((λ (pair : I01 × I01), f.to_fun (pair.snd)) ⁻¹' U) = prod {s : I01 | s ∈ I } (f.to_fun ⁻¹' U), 
     end , --begin unfold continuous,   -/
     end  
} 

def path_homotopy_inverse { x y : β} (f : path x y) (g : path x y) ( F : path_homotopy f g) : path_homotopy g f := 
{   to_fun := sorry,  ---λ st  , F.to_fun ( (1:ℝ ) - st.1 , st.2 ), --- F (1-s, t) 
    path_s := sorry,  
    at_zero := sorry, 
    at_one := sorry,  
    cont := begin unfold continuous, intro U,  sorry 
    end 
} 


def path_homotopy_comp { x y : β} (f : path x y) (g : path x y) (h : path x y) ( F : path_homotopy f g) ( G : path_homotopy g h) : 
path_homotopy f h :=
{   to_fun := sorry,  ---λ st  , fun_composer_2_closed F' G' ( F'(s,.) = F(2s,.)  ) 
    path_s := sorry,  
    at_zero := sorry, 
    at_one := sorry,  
    cont := begin unfold continuous, intro U,  sorry 
    end 
}  


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
    have HF : path_homotopy g f, 
        unfold is_homotopic_to at H, 
        let F : path_homotopy f g, 
            sorry, ----by H, , 
        exact path_homotopy_inverse f g F, 
    exact ⟨ HF ⟩ 
end 

theorem is_transitive {β  : Type*} [topological_space β ] { x y : β  } : @transitive (path x y)  (is_homotopic_to) := 
begin 
    unfold transitive, intros f g h Hfg Hgh, unfold is_homotopic_to, 
    have HF : path_homotopy f h, 
        unfold is_homotopic_to at *, 
        let F : path_homotopy f g, 
            sorry, --by Hfg existence (as nonempty)
        let G : path_homotopy g h,
            sorry, --by Hgh
        exact path_homotopy_comp f g h F G, 
    exact ⟨ HF ⟩ 
end 

theorem is_equivalence : @equivalence (path x y)  (is_homotopic_to) := 
⟨ is_reflexive, is_symmetric, is_transitive⟩ 

#print prefix equiv

#check @is_refl
#check @reflexive 
#check nonempty  

-- Associativity of homotopy 


-- Homotopy as a class ????

end homotopy


--- NEED 

/- Reparametrisation of path, homotopy cts - 
i.e. path.to_fun (2t), homotopy.to_fun (1 - s, t) cts, 
well-define and ending pts conditions-/


----------------------- Errors / Other attempts 
-- Path Homotopy
/-
structure path_homotopy2 {β} [topological_space β] { x y z w : β } ( f : path x y) ( g : path z w) := 
(to_fun : I01 × I01 →  β ) -- for product topology 
(at_zero : (function.curry to_fun) 0 = f.to_fun ) 
(at_one : (function.curry to_fun) 1 = g.to_fun )
(cont :  continuous to_fun ) 
(eq_pts : ∀ s : I01, equal_of_pts f.to_fun ((function.curry to_fun) s) ) 
--(eq_pts : ∀ s : I01, equal_of_pts_path f ((function.curry to_fun) s) ) -- check that F(s, 0)=x and F(s,1)= y
-- Type errors? 

structure path_homotopy3 {β} [topological_space β] { x y z w : β } ( f : path x y) ( g : path z w) := 
(to_fun : I01 → I01 →  β ) -- for product topology 
(at_zero : to_fun 0 = f.to_fun ) 
(at_one :  to_fun 1 = g.to_fun )
(cont :  continuous to_fun ) 
(eq_pts : ∀ s : I01, equal_of_pts f.to_fun (to_fun s) )
--(eq_pts : ∀ s : I01, equal_of_pts_path f (to_fun s) ) -/

/- 
lemma hom_is_path { f g : path x y } ( F : path_homotopy f g ) : 
∀s : I01, is_path ( f.to_fun 0) ( f.to_fun 1) ( λ t , F.to_fun (s, t) )  :=
begin 
intro s,
unfold is_path,
split,  
--rw (F s).at_zero, 
sorry ,sorry


end
#check hom_is_path -/
