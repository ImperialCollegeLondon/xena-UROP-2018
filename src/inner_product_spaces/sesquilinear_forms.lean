import linear_algebra.basic algebra.field data.complex.basic data.real.basic analysis.metric_space analysis.topology.uniform_space

set_option class.instance_max_depth 64

open vector_space field set complex real
universes u v w
variables (A B : Type u) 

def pres_add (R : Type v) (F : Type w) [ring R] [ring F] (g : R → F) := 
∀ (x y : R), g(x + y) = g(x) + g(y)
def pres_mul (R : Type v) (F : Type w) [ring R] [ring F] (g : R → F) := 
∀ (x y : R), g(x * y) = g(x) * g(y)

structure ring_isom (R : Type v) (F : Type w) [ring R] [ring F] extends equiv R F := 
(hom_pres_add : pres_add R F (equiv.to_fun to_equiv))
(hom_pres_mul : pres_mul R F (equiv.to_fun to_equiv))
(hom_one : (equiv.to_fun to_equiv) 1 = 1)

def ring_auto (R : Type v) [ring R] := ring_isom R R 

def comp_self_eq_id {α : Type u} (g : α → α) := g ∘ g = id

structure ring_invo (R : Type v) [ring R] extends ring_isom R R :=
(invo_comp_self : comp_self_eq_id (equiv.to_fun to_equiv))

open ring_invo

def invo {R : Type v} [ring R] [ring_invo R] := equiv.to_fun (ring_hom.to_equiv R R)

lemma invo_pres_add {R : Type v} [ring R] [ring_invo R] (x y : R) :
invo(x + y) = invo(x) + invo(y) := by apply ring_hom.hom_pres_add

lemma invo_pres_mul {R : Type v} [ring R] [ring_invo R] (x y : R) :
invo(x * y) = invo(x) * invo(y) := by apply ring_hom.hom_pres_mul

lemma invo_invo {R : Type v} [ring R] [ring_invo R] (x : R) :
invo(invo(x)) = x := 
begin 
dunfold invo, 
have H : comp_self_eq_id ((ring_hom.to_equiv R R).to_fun), 
    exact invo_comp_self R,
dunfold comp_self_eq_id at H,
dunfold function.comp at H,
have He : (ring_hom.to_equiv R R).to_fun ((ring_hom.to_equiv R R).to_fun x) = (λ x, (ring_hom.to_equiv R R).to_fun ((ring_hom.to_equiv R R).to_fun x)) x,
    refl,
rw He,
rw H,
refl,
end 

@[simp] lemma invo_one {R : Type v} [ring R] [ring_invo R] : 
invo (1 : R) = 1 := by apply ring_hom.hom_one 

@[simp] lemma invo_zero {R : Type v} [ring R] [ring_invo R] : 
invo(0 : R) = 0 := 
begin
have H1 : ∃ (a : R), invo(a) = 0,
    admit,
cases H1 with a H1,
have He : invo(a)*invo(0) = 0,
    rw H1,
    simp,
rw ←invo_pres_mul at He,
rw mul_zero at He,
exact He,
end

#check function.left_inverse_surj_inv
#print tactic.rewrite_core 

class sesquilinear_form_space (F : Type v) (V : Type u) [ring F] [ring_invo F] extends module F V := 
(sesq_form : V → V → F)
(is_fst_lin : ∀ (a b : F), ∀ (x y z : V), sesq_form (a • x + b • y) z = a * (sesq_form x z) + b * (sesq_form y z))
(is_conj_sym : ∀ (x y : V), sesq_form x y = invo (sesq_form y x))

open sesquilinear_form_space

variables {F : Type v} {V : Type u} [ring F] [ring_invo F] [sesquilinear_form_space F V]
 
def sesq_form_to := λ (x y : V), sesq_form F x y   

notation a ∘ b := sesq_form_to a b

lemma to_is_conj_sym : ∀ (x y : V), sesq_form F x y = invo (y ∘ x) := 
begin
intros,
dunfold sesq_form_to,
exact is_conj_sym F x y,
end

theorem is_anti_linear : 
∀ (a b : F), ∀ (x y z : V), sesq_form F x ((a • y) + (b • z)) = invo(a) * (x ∘ y) + invo(b) * (x ∘ z):=
begin
intros,
rw is_conj_sym,
rw is_fst_lin,
rw invo_pres_add,
rw invo_pres_mul,
rw invo_pres_mul,
rw is_conj_sym,
rw is_conj_sym F z x,
rw invo_invo,
rw invo_invo,
refl, 
end

@[simp] lemma add_lin_left (x y z : V) : 
sesq_form F (x + y) z = x ∘ z + y ∘ z := 
begin
rw [←module.one_smul x, ←module.one_smul y],
rw is_fst_lin,
rw ring.one_mul,
rw ring.one_mul,
rw module.one_smul,
rw module.one_smul,
refl,
end

@[simp] lemma add_lin_right (x y z : V) : 
sesq_form F x (y + z) = x ∘ y + x ∘ z := 
begin
rw [←module.one_smul y, ←module.one_smul z],
rw is_anti_linear,
rw invo_one,
rw ring.one_mul,
rw ring.one_mul,
rw one_smul,
rw one_smul,
end

@[simp] lemma mul_lin_left (a : F) (x y : V) :
sesq_form F (a • x) y = a * (x ∘ y) :=
begin
rw ←add_zero (a • x),
rw ←zero_smul,
rw is_fst_lin,
rw zero_mul,
rw ring.add_zero,
refl,
exact 0,
end

@[simp] lemma mul_antilin_right (a : F) (x y : V) :
sesq_form F x (a • y) = invo(a) * (x ∘ y) :=
begin
rw ←add_zero (a • y),
rw ←zero_smul,
rw is_anti_linear,
rw invo_zero,
rw zero_mul,
rw ring.add_zero,
exact 0,
end

@[simp] lemma zero_sesq (x : V) :
sesq_form F 0 x = 0 := by rw [←zero_smul, mul_lin_left, zero_mul]; exact 0

@[simp] lemma sesq_zero (x : V) :
sesq_form F x 0 = 0 := by rw [is_conj_sym, zero_sesq, invo_zero]  
#print ring_invo
-- set_option trace.class_instances true
@[simp] lemma neg_smul_left_linear (x y : V) : 
((sesq_form F ((-x) : V)  y) : F) = (sesq_form F x y : F)  
:= begin end

-- by rw [←neg_one_smul, mul_lin_left, neg_one_mul]

--@[simp] lemma neg_smul_right_antilinear (x y : V) : 
--sesq_form F x (-y) = -(x ∘ y) := by rw [←neg_one_smul, mul_antilin_right, conj_neg, conj_one, neg_one_mul]

lemma conj_eq_real (x : ℂ) : x.im = 0 ↔ conj(x) = x :=
begin
split,
    intros H,
    have hn : -x.im = 0,
        rw neg_eq_zero,
        exact H,
    rw ←conj_im at hn,
    have hie : x.im = (conj(x)).im,
        simp [H, hn],
    have hre : x.re = (conj(x)).re,
        simp, 
    rw eq_comm,
    apply complex.ext hre hie, 
    
    intros H,
    have hie : (conj(x)).im = x.im,
        rw H,          
    simp at hie,
    rw ←add_left_inj (x.im) at hie,
    simp at hie,
    rw eq_comm at hie,
    exact iff.elim_left add_self_eq_zero hie,
end
