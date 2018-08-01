import linear_algebra.basic algebra.field data.complex.basic data.real.basic analysis.metric_space analysis.topology.uniform_space

set_option class.instance_max_depth 128

open vector_space field set complex real
universes u v w
variables (A B : Type u) 

def pres_add (R : Type v) (F : Type w) [ring R] [ring F] (g : R → F) := 
∀ (x y : R), g(x + y) = g(x) + g(y)
def pres_mul (R : Type v) (F : Type w) [ring R] [ring F] (g : R → F) := 
∀ (x y : R), g(x * y) = g(x) * g(y)

structure ring_isom (R : Type v) (F : Type w) [ring R] [ring F] extends equiv R F := 
(isom_pres_add : pres_add R F (equiv.to_fun to_equiv))
(isom_pres_mul : pres_mul R F (equiv.to_fun to_equiv))
(isom_one : (equiv.to_fun to_equiv) 1 = 1)

def ring_auto (R : Type v) [ring R] := ring_isom R R 

def comp_self_eq_id {α : Type u} (g : α → α) := g ∘ g = id

structure ring_invo (R : Type v) [ring R] extends ring_isom R R :=
(invo_comp_self : comp_self_eq_id (equiv.to_fun to_equiv))

open ring_invo

def invo {R : Type v} [ring R] (Hi : ring_invo R) := equiv.to_fun(ring_isom.to_equiv (ring_invo.to_ring_isom Hi))

lemma invo_pres_add {R : Type v} [ring R] (Hi : ring_invo R) (x y : R) :
invo Hi (x + y) = invo Hi (x) + invo Hi (y) := by apply ring_isom.isom_pres_add

lemma invo_pres_mul {R : Type v} [ring R] (Hi : ring_invo R) (x y : R) :
invo Hi (x * y) = invo Hi (x) * invo Hi (y) := by apply ring_isom.isom_pres_mul

lemma invo_invo {R : Type v} [ring R] (Hi : ring_invo R) (x : R) :
invo Hi (invo Hi (x)) = x := 
begin 
dunfold invo, 
have H : comp_self_eq_id (((Hi.to_ring_isom).to_equiv).to_fun),
    exact invo_comp_self Hi,
dunfold comp_self_eq_id at H,
dunfold function.comp at H,
have He : (Hi.to_ring_isom.to_equiv).to_fun ((Hi.to_ring_isom.to_equiv).to_fun x) = (λ x, (Hi.to_ring_isom.to_equiv).to_fun ((Hi.to_ring_isom.to_equiv).to_fun x)) x,
    refl,
rw He,
rw H,
refl,
end 

@[simp] lemma invo_one {R : Type v} [ring R] (Hi : ring_invo R) : 
invo Hi (1 : R) = 1 := by apply ring_isom.isom_one 

@[simp] lemma invo_zero {R : Type v} [ring R] (Hi : ring_invo R) : 
invo Hi (0 : R) = 0 := 
begin
have H1 : ∃ (a : R), invo Hi (a) = 0,
    admit,
cases H1 with a H1,
have He : invo Hi (a) * invo Hi (0) = 0,
    rw H1,
    simp,
rw ←invo_pres_mul at He,
rw mul_zero at He,
exact He,
end

def id_is_equiv (R : Type v) : equiv R R := 
⟨id, id, begin dunfold function.left_inverse, intros, simp, end, begin dunfold function.right_inverse, dunfold function.left_inverse, intros, simp, end⟩

def id_is_isom (R : Type v) [ring R] : ring_isom R R := 
⟨id_is_equiv R, begin dunfold pres_add, have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end, begin dunfold pres_mul, have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end, begin have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end⟩ 

def id_is_invo (R : Type v) [ring R] : ring_invo R :=
⟨id_is_isom R, begin dunfold comp_self_eq_id, have He : ((id_is_isom R).to_equiv).to_fun = id, refl, rw He, simp end⟩ 

class sesquilinear_form_space (F : Type v) (V : Type u) [ring F] (Hi : ring_invo F) extends module F V := 
(sesq_form : V → V → F)
(is_fst_lin : ∀ (a b : F), ∀ (x y z : V), sesq_form (a • x + b • y) z = a * (sesq_form x z) + b * (sesq_form y z))
(is_conj_sym : ∀ (x y : V), sesq_form x y = invo Hi (sesq_form y x))

open sesquilinear_form_space

variables {F : Type v} {V : Type u} [ring F] (Hi : ring_invo F) [sesquilinear_form_space F V Hi]  
--notation a ∘ b := sesq_form a b

lemma to_is_conj_sym : ∀ (x y : V), sesq_form Hi x y = invo Hi (sesq_form Hi y x) := 
begin
intros,
exact is_conj_sym Hi x y,
end

theorem is_anti_linear : 
∀ (a b : F), ∀ (x y z : V), sesq_form Hi x ((a • y) + (b • z)) = invo Hi (a) * (sesq_form Hi x y) + invo Hi (b) * (sesq_form Hi x z) :=
begin
intros,
rw is_conj_sym,
rw is_fst_lin,
rw invo_pres_add,
rw invo_pres_mul,
rw invo_pres_mul,
rw is_conj_sym,
rw is_conj_sym Hi z x,
rw invo_invo,
rw invo_invo, 
end

@[simp] lemma add_lin_left (x y z : V) : 
sesq_form Hi (x + y) z = sesq_form Hi x z + sesq_form Hi y z := 
begin
rw [←module.one_smul x, ←module.one_smul y],
rw is_fst_lin,
rw ring.one_mul,
rw ring.one_mul,
rw module.one_smul,
rw module.one_smul,
end

@[simp] lemma add_lin_right (x y z : V) : 
sesq_form Hi x (y + z) = sesq_form Hi x y + sesq_form Hi x z := 
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
sesq_form Hi (a • x) y = a * sesq_form Hi x y :=
begin
rw ←add_zero (a • x),
rw ←zero_smul,
rw is_fst_lin,
rw zero_mul,
rw ring.add_zero,
exact 0,
end

@[simp] lemma mul_antilin_right (a : F) (x y : V) :
sesq_form Hi x (a • y) = invo Hi (a) * sesq_form Hi x y :=
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
sesq_form Hi 0 x = 0 := by rw [←zero_smul, mul_lin_left, zero_mul]; exact 0

@[simp] lemma sesq_zero (x : V) :
sesq_form Hi x 0 = 0 := by rw [is_conj_sym, zero_sesq, invo_zero]  

@[simp] lemma neg_smul_left_linear (x y : V) : 
sesq_form Hi (-x) y = -(sesq_form Hi x y : F) := by rw [←neg_one_smul, mul_lin_left, neg_one_mul]

@[simp] lemma neg_smul_right_antilinear (x y : V) : 
sesq_form Hi x (-y) = -(sesq_form Hi x y) := by rw [←neg_one_smul, mul_antilin_right, conj_neg, conj_one, neg_one_mul]

structure bilinear_form_space (R : Type v) (W : Type u) [ring R] extends sesquilinear_form_space R W (id_is_invo R)

def bilin_form (R : Type v) {W : Type u} [ring R] (x y : W) : R := (bilinear_form_space R W).sesq_form (id_is_equiv R) x y  

lemma bilin_bilinear (H : bilinear_form_space F V) (x y z : V) (a b : F) :
sesq_form F (a • x + b • y) z = a * (sesq_form F x z) + b * (sesq_form F y z) :=
sorry
