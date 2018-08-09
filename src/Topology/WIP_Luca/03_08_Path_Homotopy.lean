import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space
import analysis.real
import data.real.basic tactic.norm_num
import data.set.basic
import Topology.Material.subsets

universe u

open set filter lattice classical

noncomputable theory 

namespace path

variables {α  : Type*} [topological_space α ] ( x y : α )

---- PATH and I01 DEFINITION
/- The following definition of path was created by Mario Carneiro -/


def I01 := {x : ℝ | 0 ≤ x ∧ x ≤ 1}


instance : topological_space I01 := by unfold I01; apply_instance
instance : has_zero I01 := ⟨⟨0, le_refl _, zero_le_one⟩⟩
instance : has_one I01 := ⟨⟨1, zero_le_one, le_refl _⟩⟩



structure path {α} [topological_space α] (x y : α) :=
(to_fun : I01 → α)
(at_zero : to_fun 0 = x)
(at_one : to_fun 1 = y)
(cont : continuous to_fun)



instance {α} [topological_space α] (x y : α) : 
has_coe_to_fun (path x y) := ⟨_, path.to_fun⟩ 



----------

--attribute [class] path 



variables ( z w x0 : α )
variables ( g1 : path x y ) ( g2 : path z w)
variable l : I01 → α 



-- PATH INTERFACE

@[simp]
lemma start_pt_path {α} [topological_space α ] { x y : α } ( f : path x y) : f.to_fun 0 = x := f.2

@[simp]
lemma end_pt_path {α} [topological_space α ] { x y : α } ( f : path x y) : f.to_fun 1 = y := f.3


-- for later paths homotopy -- checking ending points -- Can Remove 
def equal_of_pts (f g : I01 → α ) : Prop := f 0 = g 0 ∧ f 1 = g 1

def equal_of_pts_path : Prop := equal_of_pts g1 g2

def check_pts ( x y : α ) ( g : I01 → α ) := g 0 = x ∧ g 1 = y

def check_pts_of_path ( x y : α ) ( h : path z w ) := check_pts x y h.to_fun

def equal_of_path  : Prop := g1.to_fun = g2.to_fun  -- == ? 

theorem equal {α} [topological_space α ] { x y : α } {f  g: path x y} : f = g ↔ f.to_fun = g.to_fun := 
begin 
split, intro H, rw H, intro H2, sorry, --constructor_mathching H2,   
end


-- for later paths homotopy (do not Remove)
def is_path ( x y : α ) ( f : I01 → α ) : Prop := f 0 = x ∧ f 1 = y ∧ continuous f 


def to_path { x y : α} ( f : I01 → α ) ( H : is_path x y f) : path x y := 
{  to_fun := f,
    at_zero := H.left,
    at_one := H.right.left,
    cont := H.right.right  
}

--- Can Remove
lemma cont_of_path ( g : path z w ) : continuous g.to_fun := g.cont 

--- Can Remove
def fun_of_path {α} [topological_space α ]  { x1 x2 : α  } ( g : path x1 x2 ) : I01 → α    := g.to_fun  

--------------------




--- COMPOSITION OF PATHS


variable A : set ℝ 
variables a b : I01
variable Hab : a.val < b.val  
 
----- Can Remove (unneded with T _ _ _ layering )
definition S (a b : ℝ) : set ℝ := {x : ℝ | a ≤ x ∧ x ≤ b} 


lemma lemma1 {a : I01} {b : I01} (Hab : a.val < b.val) :  a.val ∈ (S a.val b.val) := 
begin 
  show a.val ≤ a.val ∧ a.val ≤ b.val,
  split,
    exact le_of_eq rfl,
    exact le_of_lt Hab,
end
lemma lemma2 {a : I01} {b : I01} (Hab : a.val < b.val) :  b.val ∈ (S a.val b.val) := 
begin 
  show a.val ≤ b.val ∧ b.val ≤ b.val,
  split,
    exact le_of_lt Hab,
    exact le_of_eq rfl,
end 

lemma I01_bound (a : I01) (b : I01) (x : S a.val b.val) : 
0 ≤ x.val ∧ x.val ≤ 1 := 
begin 
  have H := x.property,
  split,
    exact le_trans (a.property.1 : 0 ≤ a.val) (x.property.1 : a.val ≤ x.val),
    exact le_trans (x.property.2 : x.val ≤ b.val) (b.property.2)
end

lemma lemma_sub_ba (a b : I01) {Hab : a.val < b.val } : b.val - a.val ∈ S 0 (b.val - a.val) :=  
begin split, exact sub_nonneg.2 (le_of_lt Hab), trivial end   
--------------------------------------------



-------------------------------------
-- Useful ℝ result

--- Continuity of linear functions 

theorem real.continuous_add_const (r : ℝ) : continuous (λ x : ℝ, x + r) :=
begin
  have H₁ : continuous (λ x, (x,r) : ℝ → ℝ × ℝ),
    exact continuous.prod_mk continuous_id continuous_const,
  exact continuous.comp H₁ continuous_add', 
end 

theorem real.continuous_div_const (r : ℝ) : continuous (λ x : ℝ, x / r) :=
begin
  conv in (_ / r) begin
    rw div_eq_mul_inv,
  end,
  have H₁ : continuous (λ x, (x,r⁻¹) : ℝ → ℝ × ℝ),
    exact continuous.prod_mk continuous_id continuous_const,
  exact continuous.comp H₁ continuous_mul', 
end 

theorem real.continuous_scale (a b : ℝ) : continuous (λ x : ℝ, (x + a) / b) := 
continuous.comp (real.continuous_add_const a) (real.continuous_div_const b)

theorem real.continuous_mul_const (r : ℝ) : continuous (λ x : ℝ, r*x) :=
begin 
    have H₁ : continuous (λ x, (r,x) : ℝ → ℝ × ℝ),
        exact continuous.prod_mk continuous_const continuous_id,
    show continuous ( (λ p : ℝ × ℝ , p.1 * p.2)  ∘  (λ (x : ℝ), (r,x))), 
    refine continuous.comp H₁  continuous_mul' , 

end 

theorem real.continuous_mul_const_right (r : ℝ) : continuous (λ x : ℝ, x*r) :=
begin 
    have H₁ : continuous (λ x, (x,r) : ℝ → ℝ × ℝ),
        exact continuous.prod_mk continuous_id continuous_const,
    refine continuous.comp H₁ continuous_mul' , 

end

theorem real.continuous_linear (m q : ℝ) : continuous (λ x : ℝ, m*x + q) :=
begin 
    exact continuous.comp (real.continuous_mul_const m) (real.continuous_add_const q), 
end


--- Definition of closed intervals in ℝ 

def int_clos { r s : ℝ } ( Hrs : r < s ) : set ℝ := {x : ℝ  | r ≤ x ∧ x ≤ s}


theorem is_closed_int_clos { r s : ℝ } ( Hrs : r < s ) : is_closed (int_clos Hrs) := 
begin 
let L := {x : ℝ | x ≤ s} , 
let R := {x : ℝ | r ≤ x} , 
have C1 : is_closed L, exact is_closed_le' s, 
have C2 : is_closed R, exact is_closed_ge' r, 
have Int : int_clos Hrs =  R ∩ L, 
    unfold has_inter.inter set.inter , unfold int_clos, simp,  
rw Int, exact is_closed_inter C2 C1, 
end 
#check subtype.topological_space
lemma is_closed_I01 : is_closed I01 := 
begin exact @is_closed_int_clos 0 1 (by norm_num) end 


---------------------
-------------------------------------------------------

-- Define closed subintervals of I01 = [0, 1] 
definition T ( a b : ℝ ) ( Hab : a < b ) : set I01 :=  { x : I01 | a ≤ x.val ∧ x.val ≤ b }  

-- Prove any T r s Hrs is closed in I01
lemma T_is_closed  { r s : ℝ } ( Hrs : r < s )  : is_closed (T r s Hrs) := 
begin 
let R := {x : ↥I01 | r ≤ x.val }, let L := {x : ↥I01 |  x.val ≤ s } , 
have C1 : is_closed L, 
  rw is_closed_induced_iff,
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
    exact le_trans H.2 (min_le_right _ _),
have C2 : is_closed R, 
    rw is_closed_induced_iff,
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
        intro H, exact (max_le_iff.1 H.1).2, 

have Int : T r s Hrs = set.inter R L, unfold T set.inter, simp, 
exact (is_closed_inter C2 C1), 
end 

-- Reparametrisation from T _ _ _ to I01
definition par {r s : ℝ} (Hrs : r < s) : T r s Hrs → I01 :=  
λ x, ⟨ (x.val - r)/(s - r) , begin 
have D1 : 0 < (s - r) , 
    apply sub_pos.2 Hrs, 
have D2 : 0 < (s - r)⁻¹, 
    exact inv_pos D1,   
have N1 : 0 ≤ ((x.val : ℝ ) - r), 
    exact sub_nonneg.2 (x.property.1), 
have N2 : (x.val : ℝ )- r ≤ s - r,
    have this : -r ≤ -r, trivial, 
    show (x.val : ℝ ) + - r ≤ s + - r,
    exact add_le_add (x.property.2) this,  
split, 
    show  0 ≤ ((x.val : ℝ ) - r) * (s - r)⁻¹, 
        exact mul_nonneg N1 (le_of_lt D2),  
    have H1 : 0 < (s - r), 
        exact sub_pos.2 Hrs,
    have H2 : ((x.val : ℝ ) - r) / (s - r) ≤ (s - r) / (s - r),
    exact @div_le_div_of_le_of_pos _ _ ((x.val : ℝ ) - r) (s - r) (s - r) N2 H1,
    rwa [@div_self _ _ (s - r) (ne.symm ( @ne_of_lt _ _ 0 (s - r) H1) ) ] at H2

end ⟩  



-- Continuity of reparametrisation (later employed in compositions of path/homotopy)
lemma continuous_par {r s : ℝ} (Hrs : r < s) : continuous ( par Hrs ) := 
begin unfold par,
  apply continuous_subtype_mk,
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
begin unfold T, exact set.mem_sep 
    (begin simp [has_mem.mem, -one_div_eq_inv], unfold set.mem, norm_num, end ) 
    (begin norm_num end ), 
end 


lemma help_half_T2 : ( ⟨ 1/2, help_01⟩  : I01) ∈ T (1/2) 1 T2._proof_1 := 
begin unfold T, exact set.mem_sep 
    (begin simp [has_mem.mem, -one_div_eq_inv], unfold set.mem, norm_num, end ) 
    (begin norm_num end ), 
end 

--- Intersection and covering of T1, T2

lemma inter_T : set.inter T1 T2 = { x : I01 | x.val = 1/2 } 
:= 
begin unfold T1 T2 T set.inter, simp [mem_set_of_eq, -one_div_eq_inv], apply set.ext, intro x, split, 
    rw mem_set_of_eq , rw mem_set_of_eq, simp [-one_div_eq_inv], intros A B C D, have H : x.val < 1 / 2 ∨ x.val = 1/2, 
        exact  lt_or_eq_of_le B, exact le_antisymm  B C,    
    rw mem_set_of_eq , rw mem_set_of_eq, intro H, rw H, norm_num,
end


lemma cover_I01 : T1 ∪ T2 = set.univ := 
begin 
unfold univ, unfold has_union.union , unfold T1 T2 T, apply set.ext, intro x,unfold set.union,  simp [mem_set_of_eq , -one_div_eq_inv], 
    split, intro H, simp [has_mem.mem], 
intro B, simp [has_mem.mem] at B, unfold set.mem at B, --unfold I01 at x, 
have H : 0≤ x.val ∧ x.val ≤ 1, exact x.property, simp [or_iff_not_imp_left, -one_div_eq_inv], 
intro nL, have H2 : (1 / 2 :ℝ )< x.val, exact nL H.1, exact ⟨ le_of_lt H2, H.2 ⟩ ,
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

def fgen_path {α } [topological_space α ] { x y : α }{r s : ℝ} (Hrs : r < s)(f : path x y ) : T r s Hrs → α := 
λ t, f.to_fun ( par Hrs t)

lemma pp_cont { x y : α }{r s : ℝ} (Hrs : r < s)(f : path x y ) : continuous (fgen_path Hrs f) := begin
unfold fgen_path, 
exact continuous.comp (continuous_par Hrs) f.cont, 
end 

definition fa_path { x y : α } (f : path x y ) : T1 → α := λ t, f.to_fun (par T1._proof_1  t)

lemma CA { x y : α } (f : path x y ) : continuous ( fa_path f):= 
begin 
unfold fa_path, exact continuous.comp (continuous_par T1._proof_1 ) f.cont, 
end 

definition fb_path { x y : α }(f : path x y ) : T2 → α := λ t, f.to_fun (par T2._proof_1  t)

lemma CB { x y : α } (f : path x y ) :  continuous ( fb_path f):= 
begin 
unfold fb_path, exact continuous.comp (continuous_par T2._proof_1 ) f.cont, 
end 

----- Composition of Path function 

definition comp_of_path {α} [topological_space α] { x y z : α } ( f : path x y )( g : path y z ) : path x z :=  
{   to_fun := λ t, ( paste  cover_I01 ( fa_path f ) ( fb_path g ) ) t ,  

    at_zero := 
    begin unfold paste, rw dif_pos,  
    unfold fa_path,   
    rw eqn_start, exact f.at_zero,      
    end, 

    at_one := 
    begin unfold paste, rw dif_neg,  
    unfold fb_path, show @path.to_fun α _inst_2 y z g (par  T2._proof_1 (@subtype.mk ↥I01 (λ (x : ↥I01), x ∈ T2) 1 help_T2)) = z,
    simp [eqn_end], --- exact g.at_one, 
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
        simp [eqn_1, eqn_2, -one_div_eq_inv],  --rw [f.at_one, g.at_zero], 
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

#check mul_one

lemma help_inv (y : ℝ ) : ( 1 - y) = (-1) * y + 1 := by simp 

theorem continuous_par_inv : continuous (par_inv ) := 
begin unfold par_inv, apply continuous_subtype_mk,
show continuous ((λ ( y: ℝ ), 1 - y ) ∘ (λ (x : ↥I01), x.val)), 
refine continuous.comp continuous_subtype_val _, --
conv in ( (1:ℝ)-_) 
    begin 
    rw help_inv,
    end , 
exact continuous.comp (real.continuous_mul_const (-1) ) (real.continuous_add_const 1), 
end


definition inv_of_path {α} [topological_space α] { x y : α } ( f : path x y ) : path y x :=  
{   to_fun := λ t , f.to_fun ( par_inv t ) , --  or better f.to_fun ∘ par_inv

    at_zero := begin rw eqn_1_par_inv, exact f.at_one end , 
   
    at_one := begin rw eqn_2_par_inv, exact f.at_zero end, 

    cont := by exact continuous.comp continuous_par_inv f.cont 

}







-- LOOP 

-- Definition of loop 
--- (Extends path?)
------------

/- 
structure loop {α} [topological_space α] (x : α) { y : α } extends  path x y  := 
(base_pt : to_fun 0 = x ∧ to_fun 1 = x) -/ 

/- structure loop {α} [topological_space α] (x : α) :=
(to_fun : I01 → α)
(base_pt : to_fun 0 = x ∧ to_fun 1 = x)
(cont : continuous to_fun)
-/


def is_loop ( g : path x y) : Prop := x = y -- function to check loop

/- 
structure loop3 {α} [topological_space α] (x : α) extends path x x := 
(base_pt : to_fun 0 = x ∧ to_fun 1 = x) -/ 
--(base_pt : is_loop )


--@[simp]
def loop {α} [topological_space α] (x0 : α) : Type* := path x0 x0 

def loop_const {α} [topological_space α] (x0 : α) : loop x0 := 
{   to_fun:= λ t, x0 ,  
    at_zero :=  by refl , 
    at_one := by refl, 
    cont := continuous_const   
} 


-- lemma 
-- instance loop_is_path (l1 : loop3 x0) : path x0 x0  := l1.to_path 



end path


----------------------------

----------------------------

namespace homotopy  
open path 

variables {α  : Type*} [topological_space α ] 
variables {β  : Type*} [topological_space β ] ( x y : β  )
variables ( z w x0 : β  )
variable s : I01 



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

--F.to_fun (par T1._proof_1 ⟨s, _⟩, 1) = y

/- Alternative definitions
structure path_homotopy2 {β} [topological_space β] { x y : β } ( f : path x y) ( g : path x y) := 
(to_fun : I01 → I01 →  β )
(path_s : ∀ s : I01, is_path x y ( λ t, to_fun s t ) ) 
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
#check I 


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

lemma help_hom_1 {s t : I01} (H : s ∈ T1) : (s, t) ∈ set.prod T1 I := begin simp, exact H   end

lemma prod_T1_is_closed : is_closed (set.prod T1 I) := begin simp [T1_is_closed, is_closed_prod]  end

lemma prod_T2_is_closed : is_closed (set.prod T2 I) := begin simp [T2_is_closed, is_closed_prod] end

lemma prod_inter_T : set.inter (set.prod T1 I) (set.prod T2 I) = set.prod  { x : I01 | x.val = 1/2 } I := 
begin unfold T1 T2 T set.inter set.prod, simp [mem_set_of_eq, -one_div_eq_inv], apply set.ext, intro x, split,
  {rw mem_set_of_eq , rw mem_set_of_eq, simp [-one_div_eq_inv], intros A B C D, have H : x.1.val < 1 / 2 ∨ x.1.val = 1/2, 
        exact  lt_or_eq_of_le B, exact le_antisymm  B C,    
  }, { rw mem_set_of_eq , rw mem_set_of_eq, intro H, rw H, norm_num }
end

--set_option trace.simplify.rewrite false

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

------------------------------------------------------

---- EQUIVALENCE OF HOMOTOPY



definition is_homotopic_to { x y : β } (f : path x y) ( g : path x y) : Prop := nonempty ( path_homotopy f g) 


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
            exact classical.choice H, 
        exact path_homotopy_inverse f g F, 
    exact ⟨ HF ⟩ 
end 

theorem is_transitive {β  : Type*} [topological_space β ] { x y : β  } : @transitive (path x y)  (is_homotopic_to) := 
begin 
    unfold transitive, intros f g h Hfg Hgh, unfold is_homotopic_to, 
    have HF : path_homotopy f h, 
        unfold is_homotopic_to at *, 
        let F : path_homotopy f g, 
            exact classical.choice Hfg, 
        let G : path_homotopy g h,
            exact classical.choice Hgh,
        exact path_homotopy_comp  F G, 
    exact ⟨ HF ⟩ 
end 

theorem is_equivalence : @equivalence (path x y)  (is_homotopic_to) := 
⟨ is_reflexive, is_symmetric, is_transitive⟩ 

--local notation `≈` := is_homotopic_to _ _ 

end homotopy

---------------------------------------------------
---------------------------------------------------

---- FUNDAMENTAL GROUP 


namespace fundamental_group
open homotopy
open path 
variables {α  : Type*} [topological_space α ] {x : α }


--- Underlying Notions 

lemma setoid_hom {α : Type*} [topological_space α ] (x : α )  : setoid (loop x) := setoid.mk is_homotopic_to (is_equivalence x x)

--@[simp]
def space_π_1 {α : Type*} [topological_space α ] (x : α ) := quotient (setoid_hom x)
#print prefix quotient

/- def hom_eq_class2 {α : Type*} [topological_space α ] {x : α } ( f : loop x ) : set (path x x) := 
{ g : path x x | is_homotopic_to f g } -/ 

def eq_class {α : Type*} [topological_space α ] {x : α } ( f : loop x ) : space_π_1 x := @quotient.mk (loop x) (setoid_hom x) f 

def out_loop {α : Type*} [topological_space α ] {x : α } ( F : space_π_1 x ) : loop x := @quotient.out (loop x) (setoid_hom x)  F 


def id_eq_class {α : Type*} [topological_space α ] (x : α )  : space_π_1 x := eq_class (loop_const x)


def inv_eq_class {α : Type*} [topological_space α ] {x : α } (F : space_π_1 x) : space_π_1 x := eq_class (inv_of_path (out_loop F))


-- Multiplication 

def und_mul {α : Type*} [topological_space α ] (x : α )  ( f : loop x ) ( g : loop x ) :  space_π_1 x := 
eq_class (comp_of_path f g) 


def mul2 {α : Type*} [topological_space α ] {x : α }  : space_π_1 x → space_π_1 x → space_π_1 x := 
begin 
intros F G, let f := out_loop F , let g := out_loop G, 
exact eq_class ( comp_of_path f g )  
end 

def mul {α : Type*} [topological_space α ] {x : α } : space_π_1 x → space_π_1 x → space_π_1 x := 
λ F G,  und_mul x (out_loop  F) (out_loop  G)

#print mul2 

#print prefix quotient 
#print ≈ 
#print has_equiv.equiv
#print setoid.r 

--------
---- Repar 


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
    }, rw (@mul_comm _ _ (1 - (st.fst).val)  (φ.to_fun (st.snd)).val), simp [@mul_add ℝ _ ((φ.to_fun (st.snd)).val )  (1:ℝ ) (- st.fst.val) ], rw mul_comm ((φ.to_fun (st.snd)).val ) ((st.fst).val), 
      sorry, --rw mul_add 
    --have H1: (φ.to_fun (st.snd)).val + ((st.fst).val * (st.snd).val + -((φ.to_fun (st.snd)).val * (st.fst).val)) ≤ 

/- refine calc 
(st.fst).val * (st.snd).val + (φ.to_fun (st.snd)).val * (1 + -(st.fst).val) =  (st.fst).val * (st.snd).val + (φ.to_fun (st.snd)).val* (1:ℝ ) + (φ.to_fun (st.snd)).val * - (st.fst).val  : begin     end---rw [@mul_add ℝ _ ((φ.to_fun (st.snd)).val )  (1:ℝ ) (- st.fst.val) _], end
... ≤ 1-/ 

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

-- Define homtopy from f φ to f , for any repar φ 
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


theorem repar_path_is_homeq {α : Type*} [topological_space α ] {x y : α } ( f : path x y)( φ : repar_I01 ) 
: is_homotopic_to (repar_path f φ ) f := 
begin unfold is_homotopic_to, exact nonempty.intro (hom_repar_path_to_path f φ ),  end 

------------------------------

-- Identity Elememt 

#print prefix path

-- right identity - mul_one

def p1 : repar_I01 := 
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
def hom_f_to_f_const {α : Type*} [topological_space α ] {x y : α } ( f : path x y) : path_homotopy (comp_of_path f (loop_const y)) f:= 
begin 
have H : comp_of_path f (loop_const y) = repar_path f p1, 
  { apply equal.2, unfold comp_of_path repar_path, simp, unfold fa_path fb_path fgen_path loop_const p1, simp, unfold par, funext,  
  unfold paste,  split_ifs, simp [-one_div_eq_inv], simp,
     }, 
rw H, exact hom_repar_path_to_path f p1, 

end


-- f ⬝ c ≈ f by using homotopy f → f ⬝ c above
lemma path_const_homeq_path {α : Type*} [topological_space α ] {x y : α } ( f : path x y)  : is_homotopic_to (comp_of_path f (loop_const y)) f := 
begin  unfold is_homotopic_to, refine nonempty.intro (hom_f_to_f_const f), end 


#check quotient.exists_rep
#check quotient.induction_on
#check quotient.out_eq
#check setoid


-- Now prove [f][c] = [f]

theorem mul_one {α : Type*} [topological_space α ] {x : α } ( F : space_π_1 x) : mul F (id_eq_class x) = F := 
begin unfold mul und_mul eq_class, have H : F = ⟦ quotient.out _ (setoid_hom x) F ⟧, 
--- Code below does not lead to much progress atm
 refine quotient.induction_on _ (setoid_hom x) _ F , 
 have f := @quotient.out (loop x) (setoid_hom x) F , 
 have H : F = @quotient.mk _ (setoid_hom x) f , 
 refine eq.symm _ , refine quotient.out_eq _ (setoid_hom x) F , 


 simp [@quotient.exists_rep (loop x) (setoid_hom x) F], 
apply @quotient.out (loop x) (setoid_hom x) , 

unfold mul und_mul  eq_class, let f := out_loop F , have H : F = eq_class f, unfold eq_class,   -- simp [@quotient.out_eq F, eq.symm], 


--have Hf: f = out_loop F, trivial, subst Hf, 
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



#print group

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



#check continuous
#print prefix equiv
#print prefix quotient 
#print notation  ≈ 

#print has_equiv.equiv 
    

#check @is_refl
#check @reflexive 
#check nonempty  

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
