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

section Mario

variables {α  : Type*} [topological_space α ] ( x y : α )

---- 
/- The following definition of path was created by Mario Carneiro -/


def I01 := {x : ℝ | 0 ≤ x ∧ x ≤ 1}

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

def equal_of_pts_path : Prop := equal_of_pts g1 g2

def check_pts ( x y : α ) ( g : I01 → α ) := g 0 = x ∧ g 1 = y

def check_pts_of_path ( x y : α ) ( h : path z w ) := check_pts x y h.to_fun

def equal_of_path  : Prop := g1.to_fun = g2.to_fun  -- == ? 

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

/- Lean: Server has stopped due to signal SIGSEGV. 
The lean.executablePath may be incorrect, make sure it is a 
valid Lean executable-/


-- REPARAMETRISATION of PATHS 
/-  1 Par function [a, b] to [0,1]  
       - Any f x = c * x + d cts
       - Resemble to par_path
    2 Define "special path" maker employing par_path (eg defined on [0, 1/2] )  
    
    3 Define comp of path ( f ∙ g ) by pasting_lemma; i.e. 
        fun_composer f'.to_fun g'.to_fun (where f', g' are the  "special path"s 
        of f and g respectively)  -/  

 




--- COMPOSITION OF PATHS

/- variable A_r : set ℝ 
variable A : subtype A_r 
-/

variable A : set ℝ 
variables a b : I01
variable Hab : a.val < b.val  
 

--definition S (a b : I01 ) : set ℝ := {x : ℝ | a.val ≤ x ∧ x ≤ b.val} 
definition S (a b : ℝ) : set ℝ := {x : ℝ | a ≤ x ∧ x ≤ b} 

--definition T (a b : I01 ) : set ℝ := {x : ℝ | 0 ≤ x ∧ x ≤ b.val - a.val}
--definition S (a b : ℝ ) : subtype (p) := {x : p // a ≤ x ∧ x ≤ b}

---lemma top_spa : topological_space (↑S ):= sorry
--- want/need {Hab : a.val < b.val }? 
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

-- or define as inductive type??
definition T ( a b : ℝ ) ( Hab : a < b ) : set I01 :=  { x : I01 | a ≤ x.val ∧ x.val ≤ b }  

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

#check sub_eq_add_neg
set_option trace.simplify.rewrite true



/-
lemma par_right_values (r s : I01 ) (Hrs  : r.val < s.val ) : (par Hrs) r = 0 ∧ (par Hrs) ⟨ s , _ ⟩  = 1 := 
begin
  split,
  { rw H,
    apply subtype.eq,
    unfold par,
    show (a.val + -a.val) / (b.val + -a.val) = 0,
    rw add_neg_self,
    exact zero_div _
  },
  { rw H,
    apply subtype.eq,
    unfold par,
    show (b.val + -a.val) / (b.val + -a.val) = 1,
    refine div_self _,
    rw ←sub_eq_add_neg,
    intro H2,
    rw sub_eq_zero at H2,
    rw H2 at Hab,
    exact lt_irrefl a.val Hab,
  }
end -/ 



/- 
lemma par_right_values {a b : I01} {Hab : a.val < b.val } { f : S a.val b.val → I01 } ( H : f = @par a.val b.val Hab ) : 
f ⟨ a.val , lemma1 Hab ⟩ = 0 ∧ f ⟨ b.val , lemma2 Hab⟩ = 1 := 
begin
  split,
  { rw H,
    apply subtype.eq,
    unfold par,
    show (a.val + -a.val) / (b.val + -a.val) = 0,
    rw add_neg_self,
    exact zero_div _
  },
  { rw H,
    apply subtype.eq,
    unfold par,
    show (b.val + -a.val) / (b.val + -a.val) = 1,
    refine div_self _,
    rw ←sub_eq_add_neg,
    intro H2,
    rw sub_eq_zero at H2,
    rw H2 at Hab,
    exact lt_irrefl a.val Hab,
  }
end -/ 

/- 
lemma par_right_values_R {r s : ℝ } {Hrs : r < s} { f : S r s → I01 } ( H : f = par Hrs ) : 
f ⟨ r , lemma1 Hrs ⟩ = 0 ∧ f ⟨ b.val , lemma2 Hab⟩ = 1 := 
begin
  split,
  { rw H,
    apply subtype.eq,
    unfold par,
    show (a.val + -a.val) / (b.val + -a.val) = 0,
    rw add_neg_self,
    exact zero_div _
  },
  { rw H,
    apply subtype.eq,
    unfold par,
    show (b.val + -a.val) / (b.val + -a.val) = 1,
    refine div_self _,
    rw ←sub_eq_add_neg,
    intro H2,
    rw sub_eq_zero at H2,
    rw H2 at Hab,
    exact lt_irrefl a.val Hab,
  }
end -/

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

#check @continuous_subtype_val
#check @continuous_subtype_mk
#print prefix set.

variable o : T 0 (1/2:ℝ  ) (by norm_num) 

--set_option trace.simplify.rewrite true
--set_option pp.implicit true
lemma continuous_par {r s : ℝ} (Hrs : r < s) : continuous ( par Hrs ) := 
begin unfold par,
  apply continuous_subtype_mk,
  show continuous (λ (x :  ↥(T r s Hrs)), ((x.1:ℝ ) - r) / (s - r)),
  show continuous ((λ ( y: ℝ ), (y - r) / (s - r)) ∘ (λ (x : ↥(T r s Hrs)), x.val.val)), 
  have H : continuous (λ (x : ↥(T r s Hrs)), x.val.val), 
    exact continuous.comp continuous_subtype_val continuous_subtype_val , 
  exact continuous.comp H (real.continuous_scale (-r) (s-r)), 
    
  --show continuous ((λ ( y: ℝ ), (y - r) / (s - r)) ∘ ((λ (x : ↥I01), (x.val : ℝ ) ) ∘ (λ (x : ↥(T r s Hrs)), (x.val : ↥I01) ))), 
  --have H : (λ (x : ↥(T r s Hrs)), x.val.val) = (λ (x : ↥I01), (x.val: ℝ ) )∘ (λ (x : ↥(T r s Hrs)), (x.val : ↥I01) ), 

  --show continuous ((λ ( y: ℝ ), (y - r) / (s - r)) ∘ ( (λ (x : ↥I01), x.val) ∘ (λ (x : ↥(T r s Hrs)), (⟨ x.val , _ ⟩   : I01) ) ), 
  --try to rewrite in terms of 2 lifts? 
  
  
  --refine continuous.comp continuous_subtype_val (real.continuous_scale (-r) (s-r)), 
    
  --problem of 2 lifts breaks down continuous.comp
end 

--definition T ( a b : ℝ ) ( Hab : a < b ) : set I01 :=  { x : I01 | a ≤ x.val ∧ x.val ≤ b }  

def T1 : set I01 := T 0 (1/2: ℝ ) ( by norm_num  )

def T2 : set I01 := T (1/2: ℝ ) 1 ( by norm_num  )


def int_clos { r s : ℝ } ( Hrs : r < s ) : set ℝ := {x : ℝ  | r ≤ x ∧ x ≤ s}

#print has_inter.inter  

/- variables [topological_space α] [partial_order α] [t : ordered_topology α]
lemma is_closed_Icc {a b : α} : is_closed (Icc a b) :=
is_closed_inter (is_closed_ge' a) (is_closed_le' b) -/ 

#check @is_closed_le'
#print prefix set


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

lemma is_closed_I01 : is_closed I01 := 
begin exact @is_closed_int_clos 0 1 (by norm_num) end 

#print prefix min 
---------------------
local attribute classical.prop_decidable 
--{ S:  s ∈ I01 } {R : r ∈ I01}
lemma T_is_closed  { r s : ℝ } ( Hrs : r < s )  : is_closed (T r s Hrs) := 
begin 
let R := {x : ↥I01 | r ≤ x.val }, let L := {x : ↥I01 |  x.val ≤ s } , 
/- let u := if 1< s then 1 else if s < 0 then 0 else s,  let l := max (0:ℝ ) r, have H2:  L = {x : ↥I01 | x.val ≤ u}, 
simp [u] at L, simp [l] at R, -/ 
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
    
       /-    {cases if s ∈ I01 then  (begin end)

    else sorry}-/ 
    --have P1: partial_order I01, unfold I01, by apply_instance
    
--exact @is_closed_le' ↥I01 (begin apply_instance end) (begin sorry end) (begin sorry end) ⟨ s , begin sorry end ⟩   , 
    --- @is_closed_le' ↥I01 _ _ ... may only get is_closed {b : ↥I01 | b ≤ ⟨s, ?m_1⟩} instead of is_closed {x : ↥I01 | x.val ≤ s}
/-     sorry, 
have C2 : is_closed R, 
    sorry,  
have Int : T r s Hrs = set.inter R L, unfold T set.inter, simp, 

exact (is_closed_inter C2 C1), -/ 
sorry, sorry,
end 

lemma T_is_closed2  { r s : ℝ } ( Hrs : r < s ): is_closed (T r s Hrs) :=  
begin 
--unfold T, 
--- have L : T r s Hrs = set.inter univ (int_clos Hrs), 
-- error as T r s Hrs : set I01

-- IDEA: Write in terms of intersection with I01 (i.e. T r s Hrs =  I01 ∧  closed_int Hrs), resolving subset nesting problem 
    -- Prove auxilliary lemma that (closed_int Hrs) is indeed closed 
        -- Use is_closed_inter to prove this lemma  
--have Int : {x : ↥I01 | r ≤ x.val ∧ x.val ≤ s} = set.inter univ  (closed_int Hrs) , 
sorry, 
end 

lemma T_is_closed3  { r s : ℝ } ( Hrs : r < s ): is_closed (T r s Hrs) :=  
begin 
unfold T, sorry 
end 

#print lattice.has_bot.bot  
#check nhds
#print notation ⨅ 


-----------------

lemma T1_is_closed : is_closed T1 := 
begin unfold T1, exact T_is_closed _, end 

lemma T2_is_closed : is_closed T2 := 
begin unfold T2, exact T_is_closed _, end 

lemma help_T1 : (0 : I01) ∈ T 0 (1/2) T1._proof_1 := 
begin unfold T, rw mem_set_of_eq, show 0 ≤ (0:ℝ)  ∧ ( 0:ℝ ) ≤ 1 / 2, norm_num,  end 

lemma help_T2 : (1 : I01) ∈ T (1 / 2) 1 T2._proof_1 := 
begin unfold T, rw mem_set_of_eq, split, show 1/2 ≤ (1:ℝ) , norm_num, show (1:ℝ )≤ 1, norm_num,  end 


lemma help_01 : (1 / 2 :ℝ) ∈ I01 := begin unfold I01, rw mem_set_of_eq, norm_num end
--lemma help_02 : ⟨ (1 / 2 :ℝ ), help_01⟩ ∈ T 0 (1 / 2 : ℝ ) T1._proof_1 := begin end 

lemma help_02 : (1:I01) ∉ T1 := begin unfold T1 T,rw mem_set_of_eq, show ¬(0 ≤ (1:ℝ ) ∧ (1:ℝ) ≤ 1 / 2) , norm_num,  end 

#print prefix set
--set_option pp.implicit true
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

lemma inter_T : set.inter T1 T2 = { x : I01 | x.val = 1/2 } 
:= 
begin unfold T1 T2 T set.inter, simp [mem_set_of_eq, -one_div_eq_inv], apply set.ext, intro x, split, 
    rw mem_set_of_eq , rw mem_set_of_eq, simp [-one_div_eq_inv], intros A B C D, have H : x.val < 1 / 2 ∨ x.val = 1/2, 
        exact  lt_or_eq_of_le B, exact le_antisymm  B C,    
    rw mem_set_of_eq , rw mem_set_of_eq, intro H, rw H, norm_num,
end


lemma eqn_start : par T1._proof_1 ⟨0, help_T1⟩ = 0 := 
begin unfold par, simp [-one_div_eq_inv], exact subtype.mk_eq_mk.2 (begin exact zero_div _,  end  ), end  

lemma eqn_1 : par T1._proof_1 ⟨⟨1 / 2, begin unfold I01, rw mem_set_of_eq, norm_num end⟩, begin unfold T, rw mem_set_of_eq, show 0 ≤ (1/2 : ℝ ) ∧ (1/2 : ℝ ) ≤ 1 / 2 ,  norm_num end ⟩ 
= 1 :=  begin unfold par, simp [-one_div_eq_inv], exact subtype.mk_eq_mk.2 (begin exact div_self (begin norm_num, end), end) end 

lemma eqn_2 : par T2._proof_1 ⟨⟨1 / 2, help_01  ⟩, begin unfold T, rw mem_set_of_eq, show 1/2 ≤ (1/2 : ℝ ) ∧ (1/2 : ℝ ) ≤ 1  ,  norm_num end⟩ 
= 0 := begin unfold par, simp [-one_div_eq_inv], exact subtype.mk_eq_mk.2 (by refl) end 

lemma eqn_end : par T2._proof_1 ⟨1, help_T2 ⟩ = 1 :=  
begin unfold par, exact subtype.mk_eq_mk.2 ( begin show ( ( 1:ℝ ) - 1 / 2) / (1 - 1 / 2) = 1,  norm_num, end ),  end 



lemma cover_I01 : T1 ∪ T2 = set.univ := 
begin 
unfold univ, unfold has_union.union , unfold T1 T2 T, apply set.ext, intro x,unfold set.union,  simp [mem_set_of_eq , -one_div_eq_inv], 
    split, intro H, simp [has_mem.mem], 
intro B, simp [has_mem.mem] at B, unfold set.mem at B, --unfold I01 at x, 
have H : 0≤ x.val ∧ x.val ≤ 1, exact x.property, simp [or_iff_not_imp_left, -one_div_eq_inv], 
intro nL, have H2 : (1 / 2 :ℝ )< x.val, exact nL H.1, exact ⟨ le_of_lt H2, H.2 ⟩ ,
end 

#print prefix or
#check le_of_lt

def fgen_path {α } [topological_space α ] { x y : α }{r s : ℝ} (Hrs : r < s)(f : path x y ) : T r s Hrs  → α := λ t, f.to_fun ( par Hrs t)

lemma pp_cont { x y : α }{r s : ℝ} (Hrs : r < s)(f : path x y ) : continuous (fgen_path Hrs f) := begin
unfold fgen_path, 
exact continuous.comp (continuous_par Hrs) f.cont, 
end 

definition fa_path { x y : α } (f : path x y ) : T1 → α := --@fgen_path _ _ _ _ 0 (1/2 : ℝ ) (by norm_num) f 
λ t, f.to_fun (par T1._proof_1  t)

lemma CA { x y : α } (f : path x y ) : continuous ( fa_path f):= 
begin 
unfold fa_path, exact continuous.comp (continuous_par T1._proof_1 ) f.cont, 
end 

definition fb_path { x y : α }(f : path x y ) : T2 → α := λ t, f.to_fun (par T2._proof_1  t)

lemma CB { x y : α } (f : path x y ) :  continuous ( fb_path f):= 
begin 
unfold fb_path, exact continuous.comp (continuous_par T2._proof_1 ) f.cont, 
end 

#check div_self
#check @subtype.mk --Π {α : Sort u_2} {p : α → Prop} (val : α), p val → subtype p
#check lt_or_eq_of_le
#print prefix subtype.

set_option trace.simplify.rewrite true
--set_option pp.implicit true
definition comp_of_path {α} [topological_space α] { x y z : α } ( f : path x y )( g : path y z ) :
path x z :=  
{   to_fun := λ t, ( paste  cover_I01 ( fa_path f ) ( fb_path g ) ) t ,  

    at_zero := 
    begin unfold paste, rw dif_pos,  
    unfold fa_path,   
    rw eqn_start, exact f.at_zero,      
    end, 

    at_one := 
    begin unfold paste, rw dif_neg,  
    unfold fb_path, show @path.to_fun α _inst_2 y z g (par  T2._proof_1 (@subtype.mk ↥I01 (λ (x : ↥I01), x ∈ T2) 1 help_T2)) = z,
    simp [eqn_end], exact g.at_one, 
    exact help_02, 
    end,
    
    cont := 
    begin 
    -- both images are f.to_fun 1 = g.to_fun 0 = y 
    have HM :  match_of_fun (fa_path f) (fb_path g),  
        unfold match_of_fun,  intros x B1 B2,
        have Int : x ∈ set.inter T1 T2, exact ⟨ B1 , B2 ⟩ , 
        rwa [inter_T] at Int, 
        have V : x.val = 1/2, rwa [mem_set_of_eq] at Int, --simp [V], 
        have xeq : x = (⟨ 1/2 , help_01 ⟩ : I01 ) , apply subtype.eq, rw V, 
        unfold fa_path fb_path, simp [xeq, -one_div_eq_inv], 
        show f.to_fun (par T1._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T1⟩) = g.to_fun (par T2._proof_1 ⟨⟨1 / 2, help_01⟩, help_half_T2⟩),
        simp [eqn_1, eqn_2, -one_div_eq_inv], rw [f.at_one, g.at_zero], 
    -- Use pasting lemma via closed T1, T2    
    exact cont_of_paste T1_is_closed T2_is_closed HM (CA f) (CB g),  
    end
}

--- Inverse of path

lemma inv_in_I01 (x : I01) : 1 - x.val ∈ I01 := 
begin unfold I01, rw mem_set_of_eq, split, simp [-sub_eq_add_neg] , exact x.2.2, simp, exact x.2.1, end   

definition par_inv : I01 → I01 :=  λ x, ⟨ 1 - x.val , inv_in_I01 x ⟩ 




definition inv_of_path {α} [topological_space α] { x y : α } ( f : path x y ) : path y x :=  
{   to_fun := λ t , f.to_fun ( par_inv t ) , -- f.to_fun ∘ par_inv

    at_zero :=
    begin 
    
    
    sorry,
    end, 

    at_one := sorry, 

    cont := sorry

}


#print prefix dif_ctx_congr




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


def is_loop ( g : path x y) : Prop := x = y -- function to check loop


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


namespace homotopy  -- Homotopy

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
#check @continuous.comp 


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

#print prefix equiv

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

--local notation `≈` := is_homotopic_to _ _ 

def hom_eq_class {α : Type*} [topological_space α ] {x : α } ( f : loop3 x ) : set (path x x) := 
{ g : path x x | is_homotopic_to f g }

-- Ignore below

/- def space_π_1 {α : Type*} [topological_space α ] {x : α } :=  --: set (hom_eq_class x)
{ h : hom_eq_class ( path x x) } -/ 

/- 
def space_π_1 {α : Type*} [topological_space α ] {x : α } : set (set (path x x)) := 
{ ∀ f : loop3 x,  hom_eq_class ( f)   } -/ 

#print group 

#check continuous
#print prefix equiv
#print prefix quotient 
#print notation  ≈ 

#print has_equiv.equiv 
    

#check @is_refl
#check @reflexive 
#check nonempty  

-- Associativity of homotopy 


-- Homotopy as a class ????

end homotopy 
