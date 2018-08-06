import linear_algebra.basic

set_option class.instance_max_depth 128

open vector_space field
universes u v w

def pres_add (R : Type v) (F : Type w) [ring R] [ring F] (g : R → F) := 
∀ (x y : R), g(x + y) = g(x) + g(y)
def pres_mul (R : Type v) (F : Type w) [ring R] [ring F] (g : R → F) := 
∀ (x y : R), g(x * y) = g(x) * g(y)

structure ring_isom (R : Type v) (F : Type w) [ring R] [ring F] extends equiv R F := 
(isom_pres_add : pres_add R F (equiv.to_fun to_equiv))
(isom_pres_mul : pres_mul R F (equiv.to_fun to_equiv))
(isom_one : (equiv.to_fun to_equiv) 1 = 1)

def ring_auto (R : Type v) [ring R] := ring_isom R R 

def comp_self_eq_id {α : Type u} (g : α → α) := ∀ (x : α), g (g x) = x

structure ring_invo (R : Type v) [ring R] extends ring_isom R R :=
(invo_comp_self : comp_self_eq_id (equiv.to_fun to_equiv))

open ring_invo

def invo {R : Type v} [ring R] (Hi : ring_invo R) := equiv.to_fun(ring_isom.to_equiv (ring_invo.to_ring_isom Hi))

lemma invo_pres_add {R : Type v} [ring R] (Hi : ring_invo R) (x y : R) :
invo Hi (x + y) = invo Hi (x) + invo Hi (y) := by apply ring_isom.isom_pres_add

lemma invo_pres_mul {R : Type v} [ring R] (Hi : ring_invo R) (x y : R) :
invo Hi (x * y) = invo Hi (x) * invo Hi (y) := by apply ring_isom.isom_pres_mul

lemma invo_invo {R : Type v} [ring R] (Hi : ring_invo R) (x : R) :
invo Hi (invo Hi (x)) = x := by apply invo_comp_self
 
lemma invo_one {R : Type v} [ring R] (Hi : ring_invo R) : 
invo Hi (1 : R) = 1 := by apply ring_isom.isom_one 

lemma invo_is_bijective {R : Type v} [ring R] (Hi : ring_invo R): 
function.bijective (invo Hi) := equiv.bijective (ring_invo.to_ring_isom Hi).to_equiv

lemma invo_zero {R : Type v} [ring R] (Hi : ring_invo R) : 
invo Hi (0 : R) = 0 := 
begin
have H1 : ∃ (a : R), invo Hi (a) = 0,
    exact (invo_is_bijective Hi).right 0,
cases H1 with a H1,
have He : invo Hi (a) * invo Hi (0) = 0,
    rw H1,
    simp,
rw ←invo_pres_mul at He,
rw mul_zero at He,
exact He,
end

lemma invo_zero_iff {R : Type v} [ring R] (Hi : ring_invo R) (a : R) :
invo Hi a = 0 ↔ a = 0 := 
begin
split,
    intros H,
    rw ←invo_zero Hi at H,
    exact (function.injective.eq_iff (invo_is_bijective Hi).left).mp H,

    intros H,
    rw H,
    rw invo_zero,
end

lemma invo_neg_one {R : Type v} [ring R] (Hi : ring_invo R) : 
invo Hi (-1 : R) = -1 := 
begin
have H2 : invo Hi (-1 + 1) = 0,
    rw neg_add_self,
    rw invo_zero,
rw invo_pres_add at H2,
rw add_eq_zero_iff_eq_neg at H2,
rw invo_one at H2,
exact H2,
end

lemma invo_neg {R : Type v} [ring R] (Hi : ring_invo R) (x : R) : 
invo Hi (-x) = -(invo Hi x) :=
begin
rw ←neg_one_mul,
rw invo_pres_mul,
rw invo_neg_one,
rw neg_one_mul,
end

def id_is_equiv (R : Type v) : equiv R R := 
⟨id, id, begin dunfold function.left_inverse, intros, simp, end, begin dunfold function.right_inverse, dunfold function.left_inverse, intros, simp, end⟩

def id_is_isom (R : Type v) [ring R] : ring_isom R R := 
⟨id_is_equiv R, begin dunfold pres_add, have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end, begin dunfold pres_mul, have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end, begin have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end⟩ 

def id_is_invo (R : Type v) [ring R] : ring_invo R :=
⟨id_is_isom R, begin dunfold comp_self_eq_id, have He : ((id_is_isom R).to_equiv).to_fun = id, refl, rw He, simp end⟩ 

class sesquilinear_form_space (F : Type u) (V : Type v) [ring F] (Hi : ring_invo F) extends module F V := 
(sesq_form : V → V → F)
(fst_add_lin : ∀ (x y z : V), sesq_form (x + y) z = sesq_form x z + sesq_form y z)
(fst_mul_lin : ∀ (x y : V) (a : F), sesq_form (a • x) y = a * (sesq_form x y))
(snd_add_lin : ∀ (x y z : V), sesq_form x (y + z) = sesq_form x y + sesq_form x z)
(snd_mul_antilin : ∀ (a : F) (x y : V), sesq_form x (a • y) = (invo Hi a) * (sesq_form x y))  

open sesquilinear_form_space

lemma zero_sesq {F : Type u} {V : Type v} [ring F] (Hi : ring_invo F) [sesquilinear_form_space F V Hi] (x : V) :
sesq_form Hi 0 x = 0 := by rw [←zero_smul, fst_mul_lin, zero_mul]; exact 0

lemma sesq_zero {F : Type u} {V : Type v} [ring F] (Hi : ring_invo F) [sesquilinear_form_space F V Hi] (x : V) :
sesq_form Hi x 0 = 0 := by rw [←zero_smul, snd_mul_antilin, invo_zero, zero_mul]; exact 0

lemma sesq_neg_left {F : Type u} {V : Type v} [ring F] (Hi : ring_invo F) [sesquilinear_form_space F V Hi] (x y : V) : 
sesq_form Hi (-x) y = -(sesq_form Hi x y : F) := by rw [←neg_one_smul, fst_mul_lin, neg_one_mul]

lemma sesq_neg_right {F : Type u} {V : Type v} [ring F] (Hi : ring_invo F) [sesquilinear_form_space F V Hi] (x y : V) : 
sesq_form Hi x (-y) = -(sesq_form Hi x y) := by rw [←neg_one_smul, snd_mul_antilin, invo_neg, invo_one, neg_one_mul]

lemma sesq_sub_left {F : Type u} {V : Type v} [ring F] (Hi : ring_invo F) [sesquilinear_form_space F V Hi] (x y z : V) :
sesq_form Hi (x - y) z = sesq_form Hi x z - sesq_form Hi y z := by rw [sub_eq_add_neg, fst_add_lin, sesq_neg_left]; refl

lemma sesq_sub_right {F : Type u} {V : Type v} [ring F] (Hi : ring_invo F) [sesquilinear_form_space F V Hi] (x y z : V) :
sesq_form Hi x (y - z) = sesq_form Hi x y - sesq_form Hi x z := by rw [sub_eq_add_neg, snd_add_lin, sesq_neg_right]; refl

def is_ortho {F : Type u} {V : Type v} [ring F] (Hi : ring_invo F) [sesquilinear_form_space F V Hi] (x y : V) : Prop :=
sesq_form Hi x y = 0

theorem ortho_mul_left {F : Type u} {V : Type v} [domain F] (Hi : ring_invo F) [sesquilinear_form_space F V Hi] (x y : V) (a : F) (ha : a ≠ 0) : 
(is_ortho Hi x y) ↔ (is_ortho Hi (a • x) y) :=
begin
dunfold is_ortho,
split,
    intros H,
    rw [fst_mul_lin, H, mul_zero],

    intros H,
    rw [fst_mul_lin, mul_eq_zero] at H,
    cases H, 
        trivial, 

        exact H, 
end

theorem ortho_mul_right {F : Type v} {V : Type u} [domain F] (Hi : ring_invo F) [sesquilinear_form_space F V Hi] (x y : V) (a : F) (ha : a ≠ 0) : 
(is_ortho Hi x y) ↔ (is_ortho Hi x (a • y)) :=
begin
dunfold is_ortho,
split,
    intros H,
    rw [snd_mul_antilin, H, mul_zero],

    intros H,
    rw [snd_mul_antilin, mul_eq_zero] at H,
    cases H,
        rw invo_zero_iff at H, 
        trivial, 

        exact H, 
end
