import linear_algebra.basic algebra.field data.complex.basic data.real.basic analysis.metric_space

open vector_space field set complex real
universes u v w

class herm_inner_product_space (V : Type u) extends vector_space ℂ V :=
(inprod : V → V → ℂ) 
(is_sesquilinear : ∀ (a b : ℂ), ∀ (x y z : V), inprod (a • x + b • y) z = a * (inprod x z) + b * (inprod y z))
(is_conj_sym : ∀ (x y : V), inprod x y = conj (inprod y x))
(is_pos_def : ∀ (x : V), (inprod x x).re ≥ 0 ∧ ((inprod x x) = 0 ↔ x = 0))

notation a ∘ b := herm_inner_product_space.inprod a b

open herm_inner_product_space

theorem is_anti_linear (V : Type u) [herm_inner_product_space V] : 
∀ (a b : ℂ), ∀ (x y z : V), x ∘ ((a • y) + (b • z)) = conj(a) * (x ∘ y) + conj(b) * (x ∘ z):=
begin
intros, 
rw [is_conj_sym, is_sesquilinear, conj_add, conj_mul, ←is_conj_sym, conj_mul, ←is_conj_sym],
end

@[simp] lemma add_lin_left {V : Type u} [herm_inner_product_space V] (x y z : V) : 
(x + y) ∘ z = x ∘ z + y ∘ z := 
begin
rw [←module.one_smul x, ←module.one_smul y],
rw is_sesquilinear,
simp,
end

@[simp] lemma add_lin_right {V : Type u} [herm_inner_product_space V] (x y z : V) : 
x ∘ (y + z) = x ∘ y + x ∘ z := 
begin
rw [←module.one_smul y, ←module.one_smul z],
rw is_anti_linear,
simp,
end

@[simp] lemma mul_lin_left {V : Type u} [herm_inner_product_space V] (a : ℂ) (x y : V) :
(a • x) ∘ y = a * (x ∘ y) :=
begin
rw ←add_zero (a • x),
rw ←zero_smul,
rw is_sesquilinear,
simp,
exact 0,
end

@[simp] lemma mul_antilin_right {V : Type u} [herm_inner_product_space V] (a : ℂ) (x y : V) :
x ∘ (a • y) = conj(a) * (x ∘ y) :=
begin
rw ←add_zero (a • y),
rw ←zero_smul,
rw is_anti_linear,
simp,
exact 0,
end

@[simp] lemma zero_inprod {V: Type u} [herm_inner_product_space V] (x : V) :
0 ∘ x = 0 := by rw [←zero_smul, mul_lin_left, zero_mul]; exact 0

@[simp] lemma inprod_zero {V: Type u} [herm_inner_product_space V] (x : V) :
x ∘ 0 = 0 := by rw [is_conj_sym, conj_eq_zero, zero_inprod]  

lemma neg_smul_left_linear {V : Type u} [herm_inner_product_space V] (x y : V) : 
-x ∘ y = -(x ∘ y) := by rw [←neg_one_smul, mul_lin_left, neg_one_mul]

lemma neg_smul_right_antilinear {V : Type u} [herm_inner_product_space V] (x y : V) : 
x ∘ -y = -(x ∘ y) := by rw [←neg_one_smul, mul_antilin_right, conj_neg, conj_one, neg_one_mul]


lemma im_re_eq_imp_eq {x y : ℂ} (H1 : x.re = y.re) (H2: x.im = y.im) :
x = y :=
begin
rw [←re_add_im x, ←re_add_im y, H1, H2], 
end

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
    apply im_re_eq_imp_eq hre hie, 
    
    intros H,
    have hie : (conj(x)).im = x.im,
        rw H,          
    simp at hie,
    rw ←add_left_inj (x.im) at hie,
    simp at hie,
    rw eq_comm at hie,
    exact iff.elim_left add_self_eq_zero hie,
end

lemma ne_zero_im_zero_imp_re_ne_zero {x : ℂ} : x ≠  0 → x.im = 0 → x.re ≠ 0 :=
begin
intros H1 H2,
have Hx : x = ↑x.re,
    rw [←re_add_im x, H2, of_real_zero, zero_mul, field.add_zero, of_real_re],
rw Hx at H1,
exact of_real_ne_zero.mp H1,
end

lemma re_of_real (x : ℂ) : x.im = 0 → ↑(x.re) = x :=
begin
intros H,
rw [←re_add_im x, H, of_real_zero, zero_mul, field.add_zero, of_real_inj, of_real_re],
end

lemma ne_comm {α : Type u} (a b : α) : a ≠ b ↔ b ≠ a :=
begin
dunfold ne,
split,
    intros H,
    rw eq_comm,
    exact H,

    intros H,
    rw eq_comm,
    exact H, 
end

theorem eq_imp_real {V : Type u} [herm_inner_product_space V] :
∀ (x : V), (x ∘ x).im = 0 := 
begin
intros,
have H : conj(x ∘ x) = x ∘ x,
    rw ←is_conj_sym,
rw conj_eq_real (x ∘ x),
exact H, 
end

lemma ne_zero_iff_inprod_ne_zero {V : Type u} [herm_inner_product_space V] (x : V) : 
(x ∘ x) ≠ 0 ↔ x ≠ 0 :=
begin
split,
    intros H,
    exact (iff_false_left H).mp (is_pos_def x).right, 

    intros H,
    exact (iff_false_right H).mp (is_pos_def x).right,
end

noncomputable def herm_norm {V: Type u} [herm_inner_product_space V] (x : V) : ℝ := sqrt((x ∘ x).re)

local notation |a|  := herm_norm(a) 

open classical

theorem cauchy_schwarz_innequality {V : Type u} [herm_inner_product_space V] :
∀ (x y : V), abs((x ∘ y)) ≤ |x|*|y| := 
begin
intros,
have ho : y = 0 ∨ y ≠ 0,
    apply em,
cases ho,
    rw ho,
    dunfold herm_norm,
    simp,

    have H : 0 ≤ |x - ((x ∘ y)/(↑( |y|*|y| ))) • y| * |x - ((x ∘ y)/(↑( |y|*|y| ))) • y| ,
        dunfold herm_norm, 
        apply mul_nonneg (sqrt_nonneg (((x - (x ∘ y / ↑(sqrt ((y ∘ y).re) * sqrt ((y ∘ y).re))) • y) ∘ (x - (x ∘ y / ↑(sqrt ((y ∘ y).re) * sqrt ((y ∘ y).re))) • y)).re)) (sqrt_nonneg (((x - (x ∘ y / ↑(sqrt ((y ∘ y).re) * sqrt ((y ∘ y).re))) • y) ∘ (x - (x ∘ y / ↑(sqrt ((y ∘ y).re) * sqrt ((y ∘ y).re))) • y)).re)), 
    simp at H,
    dunfold herm_norm at H,
    rw mul_self_sqrt (is_pos_def ((x + -((x ∘ y / (↑(sqrt ((y ∘ y).re)) * ↑(sqrt ((y ∘ y).re)))) • y)))).left at H, 
    rw ←of_real_mul at H,
    rw of_real_inj.mpr (mul_self_sqrt (is_pos_def y).left) at H, 
    simp at H, 
    rw is_conj_sym (-((x ∘ y / ↑((y ∘ y).re)) • y)) at H,
    rw conj_re at H, 
    have he : (-((x ∘ y / ↑((y ∘ y).re)) • y) ∘ -((x ∘ y / ↑((y ∘ y).re)) • y)).re = -(x ∘ -((x ∘ y / ↑((y ∘ y).re)) • y)).re,
        rw neg_smul_right_antilinear,
        rw neg_smul_right_antilinear,
        rw neg_smul_left_linear,
        rw neg_neg,
        rw mul_lin_left,
        rw mul_antilin_right,
        rw mul_antilin_right,
        have hr : y ∘ y = ↑((y ∘ y).re),
            rw re_of_real (y ∘ y) (eq_imp_real y),
        rw conj_div,
        rw conj_of_real,
        rw ←hr,
        rw div_mul_cancel (conj(x ∘ y)) ((iff_false_right ho).mp (is_pos_def y).right),
        rw div_mul_eq_mul_div,
        rw div_mul_eq_mul_div,
        simp,
        rw field.mul_comm, 
    rw he at H,
    rw add_neg_self at H,
    rw field.add_zero at H,
    rw neg_smul_right_antilinear at H,
    rw mul_antilin_right at H,
    rw conj_div at H,
    rw conj_of_real at H,
    dunfold herm_norm,
    dunfold complex.abs, 
    rw ←sqrt_mul (is_pos_def x).left,
    rw sqrt_le (norm_sq_nonneg (x ∘ y)) (mul_nonneg (is_pos_def x).left (is_pos_def y).left), 
    rw ←sub_le_iff_le_add' at H,
    rw sub_eq_neg_add at H,
    rw field.add_zero at H,
    rw div_mul_eq_mul_div at H,
    rw neg_re at H,
    rw neg_le_neg_iff at H,
    rw field.mul_comm at H,
    rw mul_conj at H,
    rw ←of_real_div at H,
    rw of_real_re at H,
    rw div_le_iff (lt_of_le_of_ne (is_pos_def y).left ((ne_comm ((y ∘ y).re) 0).mp (ne_zero_im_zero_imp_re_ne_zero  ((ne_zero_iff_inprod_ne_zero y).mpr ho) (eq_imp_real y)))) at H,
    exact H,
end

class norm_space (V: Type u) extends vector_space ℂ V :=
(N : V → ℝ)
(norm_pos : ∀ (x : V), N(x) ≥ 0)
(norm_sub_add : ∀ (x y : V), N(x + y) ≤ N(x) + N(y))
(norm_abs_hom : ∀ (x : V), ∀ (a : ℂ), N(a • x) = abs(a)*N(x))
(norm_pos_def : ∀ (x : V), N(x) = 0 ↔ x = 0) 

open norm_space

noncomputable instance herm_space_is_norm_space {V : Type u} [herm_inner_product_space V] :
norm_space V := 
{ 
N := herm_norm, 
norm_pos := begin intros, exact sqrt_nonneg ((x ∘ x).re), end,  
norm_sub_add := 
    begin  
    intros,
    have H : |x + y|*|x + y| = ((x + y) ∘ (x + y)).re,
        dunfold herm_norm,
        rw mul_self_sqrt (is_pos_def (x + y)).left,
    rw add_lin_left at H,
    rw add_lin_right at H,
    rw add_lin_right at H,
    rw is_conj_sym y at H,
    rw field.add_assoc at H,
    rw ←field.add_assoc (x ∘ y) at H,
    rw add_conj at H,
    rw add_re at H,
    rw add_re at H,
    rw of_real_re at H, 
    have hle : 2*(x ∘ y).re ≤ 2*abs(x ∘ y),
        exact (mul_le_mul_left (lt_trans zero_lt_one (begin exact two_gt_one, end))).mpr (re_le_abs (x ∘ y)),
    rw ←sub_zero (2 * abs (x ∘ y)) at hle,
    rw le_sub at hle,
    have Hle : |x + y|*|x + y| + 0 ≤ (x ∘ x).re + (2 * (x ∘ y).re + (y ∘ y).re) + (2 * abs (x ∘ y) - 2 * (x ∘ y).re),
        exact add_le_add (le_of_eq H) hle,
    simp at Hle,
    rw ←field.add_assoc at Hle,
    have Hcs : 2*abs(x ∘ y) ≤ 2*|x|*|y|,
        rw field.mul_assoc,
        exact (mul_le_mul_left (lt_trans zero_lt_one (begin exact two_gt_one, end))).mpr (cauchy_schwarz_innequality x y),
    have hz : 2*abs(x ∘ y) ≥ 0,
        rw two_mul,
        have ha : abs(x ∘ y) ≥ 0,
            exact abs_nonneg (x ∘ y),
        exact le_add_of_le_of_nonneg ha ha,
    dunfold herm_norm at Hcs,
    rw ←sub_zero (2 * sqrt ((x ∘ x).re) * sqrt ((y ∘ y).re)) at Hcs,
    rw le_sub at Hcs,
    have Hs : |x + y|*|x + y| ≤ 2 * sqrt ((x ∘ x).re) * sqrt ((y ∘ y).re) - 2 * abs (x ∘ y) + ((x ∘ x).re + (y ∘ y).re + 2 * abs (x ∘ y)),
        apply le_add_of_nonneg_of_le Hcs Hle,
    simp at Hs,
    have He : (x ∘ x).re + ((y ∘ y).re + 2 * sqrt ((x ∘ x).re) * sqrt ((y ∘ y).re)) = (herm_norm(x) + herm_norm(y))*(herm_norm(x) + herm_norm(y)),
        dunfold herm_norm,
        ring,
        simp,
        rw sqr_sqrt (is_pos_def y).left,
        rw ring.right_distrib,
        rw ←sqrt_mul, 
        rw sqrt_mul_self ((is_pos_def x).left),
        ring, 
        exact (is_pos_def x).left,
    rw He at Hs,
    apply (mul_self_le_mul_self_iff (begin intros, exact sqrt_nonneg (((x + y) ∘ (x + y)).re), end) (add_nonneg (begin intros, exact sqrt_nonneg ((x ∘ x).re), end) (begin intros, exact sqrt_nonneg ((y ∘ y).re), end))).mpr Hs,      
    end, 
norm_abs_hom := 
    begin
    intros, 
    dunfold herm_norm, 
    rw mul_lin_left, 
    rw mul_antilin_right,
    rw ←field.mul_assoc,
    rw mul_re,
    rw mul_conj,
    rw of_real_im,
    rw zero_mul,
    rw sub_zero,
    simp,
    rw sqrt_mul (norm_sq_nonneg a),
    refl,
    end,
norm_pos_def := 
    begin 
    intros,
    dunfold herm_norm,
    have ho : (x ∘ x).im = 0,
        exact eq_imp_real x,
    split,
        intros H,
        rw ←sqrt_zero at H,
        rw sqrt_inj ((is_pos_def x).left) (le_of_eq (refl 0)) at H,
        rw ←zero_im at ho,
        rw ←zero_re at H,
        have hpo : x ∘ x = 0,
            exact im_re_eq_imp_eq H ho,
        exact ((is_pos_def x).right).mp hpo,

        intros hz,
        rw ←sqrt_zero,
        rw sqrt_inj ((is_pos_def x).left) (le_of_eq (refl 0)),
        have hpo : x ∘ x = 0,
            exact ((is_pos_def x).right).mpr hz,
        rw ←zero_re,
        rw hpo,
    end,
} 

def is_ortho {V : Type u} [herm_inner_product_space V] (x y : V) : Prop :=
x ∘ y = 0

notation a ⊥ b := is_ortho a b 

theorem ortho_refl_iff_zero {V : Type u} [herm_inner_product_space V] (x : V) : 
(x ⊥ x) ↔ x = 0 := by exact (is_pos_def x).right

theorem ortho_mul_left {V : Type u} [herm_inner_product_space V] (x y : V) (a : ℂ) (ha : a ≠ 0) : 
(x ⊥ y) ↔ ((a • x) ⊥ y) :=
begin
dunfold is_ortho,
split,
    intros H,
    rw [mul_lin_left, H, mul_zero],

    intros H,
    rw [mul_lin_left, mul_eq_zero] at H,
    cases H, 
        trivial, 

        exact H, 
end

theorem ortho_mul_right {V :Type u} [herm_inner_product_space V] (x y : V) (a : ℂ) (ha : a ≠ 0) : 
(x ⊥ y) ↔ (x ⊥ (a • y)) :=
begin
dunfold is_ortho,
split,
    intros H,
    rw [mul_antilin_right, H, mul_zero],

    intros H,
    rw [mul_antilin_right, mul_eq_zero] at H,
    cases H,
        rw conj_eq_zero at H, 
        trivial, 

        exact H, 
end

theorem ortho_imp_not_lindep {V :Type u} [herm_inner_product_space V] (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) : 
(x ⊥ y) → ¬∃ (a : ℂ), (a ≠ 0) ∧ (x = a • y ∨ a • x = y) :=
begin
    intros H1,
    apply not_exists.mpr,
    intros a,
    intros H2,
    dunfold is_ortho at H1,
    cases H2 with ha H2,
    cases H2,    
        rw H2 at H1,
        rw mul_lin_left at H1,
        rw mul_eq_zero at H1,
        cases H1,
            trivial, 

            exact hy (((is_pos_def y).right).mp H1),
        
        rw ←H2 at H1,
        rw mul_antilin_right at H1,
        rw mul_eq_zero at H1,
        cases H1,
            exact ha ((conj_eq_zero).mp H1),

            exact hx (((is_pos_def x).right).mp H1),
end

noncomputable def herm_dist {V : Type u} [herm_inner_product_space V] (x y : V) : ℝ := |x - y|

open metric_space

noncomputable instance herm_space_is_metric_space {V : Type u} [herm_inner_product_space V] : 
metric_space V :=
{
dist := herm_dist, 
dist_self := 
    begin
    intros, 
    dunfold herm_dist,
    dunfold herm_norm,
    simp,
    end,
eq_of_dist_eq_zero :=
    begin
    dunfold herm_dist,
    dunfold herm_norm,
    intros x y H,
    rw sqrt_eq_zero (is_pos_def (x - y)).left at H,
    rw ←zero_re at H,
    have H1 : (x - y) ∘ (x - y) = 0,
        exact im_re_eq_imp_eq H (eq_imp_real (x - y)),
    rw (is_pos_def (x - y)).right at H1,
    exact sub_eq_zero.mp H1,
    end,
dist_comm := 
    begin
    intros,
    dunfold herm_dist, 
    dunfold herm_norm,
    rw sqrt_inj (is_pos_def (x - y)).left (is_pos_def (y - x)).left,
    simp, 
    rw ←neg_one_smul,
    rw ←neg_one_smul,
    rw [mul_lin_left, mul_antilin_right], 
    rw [mul_lin_left, mul_antilin_right],
    rw [mul_lin_left, mul_antilin_right],
    rw [mul_lin_left, mul_antilin_right],
    simp,
    end,
dist_triangle := 
    begin 
    dunfold herm_dist,
    intros,
    have H : x - z = (x - y) + (y - z),
        simp,
    rw H, 
    exact norm_sub_add (x - y) (y - z),
    end,
}

 
