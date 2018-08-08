import linear_algebra.basic algebra.field data.complex.basic data.real.basic analysis.metric_space analysis.topology.uniform_space

open vector_space field set complex real
universes u v w

class semi_norm_space (V : Type u) extends module ℂ V := 
(N : V → ℝ)
(semi_norm_nonneg : ∀ (x : V), N(x) ≥ 0)
(semi_norm_sub_add : ∀ (x y : V), N(x + y) ≤ N(x) + N(y))
(semi_norm_abs_hom : ∀ (x : V), ∀ (a : ℂ), N(a • x) = abs(a)*N(x))

class norm_space (V : Type u) extends module ℂ V :=
(N : V → ℝ)
(norm_nonneg : ∀ (x : V), N(x) ≥ 0)
(norm_sub_add : ∀ (x y : V), N(x + y) ≤ N(x) + N(y))
(norm_abs_hom : ∀ (x : V), ∀ (a : ℂ), N(a • x) = abs(a)*N(x))
(norm_pos_def : ∀ (x : V), N(x) = (0 : ℝ) ↔ x = (0 : V))  

open norm_space

variables {V : Type u} [norm_space V] 

@[simp] lemma norm_zero : N(0 : V) = 0 := (norm_pos_def 0).mpr (refl 0)  

@[simp] lemma norm_neg (x : V) : N(-x) = N(x) := 
begin
rw ←neg_one_smul,
rw norm_abs_hom,
simp,
end

lemma norm_ne_zero_iff_ne_zero (x : V) :
N(x) ≠ 0 ↔ x ≠ 0 := --⟨λ H, (iff_false_left H).mp (norm_pos_def x), λ H, (iff_false_right H).mp (norm_pos_def x)⟩ 
begin
split,
    intros H,
    exact (iff_false_left H).mp (norm_pos_def x), 

    intros H,
    exact (iff_false_right H).mp (norm_pos_def x),
end

theorem norm_sub_le_sub_norm (x y : V) : complex.abs(N(x) - N(y)) ≤ N(x - y) :=
begin
rw ←of_real_sub,
rw abs_of_real,
rw abs_le,
split,
    ring,
    have Hy : N((y - x) + x) = N(y),
        simp,
    have H1 : N((y - x) + x) ≤ N(y - x) + N(x),
        exact norm_sub_add (y - x) (x), 
    rw Hy at H1,
    rw ←(add_le_add_iff_right (-N(x))) at H1,
    ring at H1,
    rw [←neg_sub, norm_neg],
    rw neg_le,
    ring,
    exact H1,


    have Hx : N((x - y) + y) = N(x),
        simp,
    have H2 : N((x - y) + y) ≤ N(x - y) + N(y),
        exact norm_sub_add (x - y) (y), 
    rw Hx at H2,
    rw ←(add_le_add_iff_right (-N(y))) at H2,
    ring at H2,
    exact H2,
end


noncomputable def norm_dist (x y : V) := N(x - y)

noncomputable instance to_metric_space : has_coe (norm_space V) (metric_space V) :=
⟨λh, {
dist := norm_dist, 
dist_self := 
    begin
    intros, 
    dunfold norm_dist,
    simp,
    end,
eq_of_dist_eq_zero :=
    begin
    dunfold norm_dist,
    intros x y H,
    exact sub_eq_zero.mp ((norm_pos_def (x - y)).mp H),
    end,
dist_comm := 
    begin
    intros,
    dunfold norm_dist,
    rw ←neg_sub,
    rw norm_neg,
    end,
dist_triangle := 
    begin 
    dunfold norm_dist,
    intros,
    have H : x - z = (x - y) + (y - z),
        simp,
    rw H, 
    exact norm_sub_add (x - y) (y - z),
    end,
} ⟩ 

def is_normalised (x : V) := N(x) = 1 

noncomputable def normalise (x : V) := ↑(N(x))⁻¹ • x 

def normalise_set :
set V → set V := image(normalise)

lemma normalised_linear_indep (s : set V) :
linear_independent s → linear_independent (normalise_set s) :=
begin
dunfold linear_independent,
intros H1 l H3 H4, 
have H5 : ∀ (x : V), x ∉ s → x ∈ normalise_set s,
    intros x hx,
end

#print finsupp.sum
#print finsupp
#print coe_fn


lemma normalised_span_spans (s : set V) : 
span s = span (normalise_set s) :=
begin
rw set_eq_def,
intros,
dunfold span, 
split,
    intros H,
    rw mem_set_of_eq at H,
    apply exists.elim H,
    intros v Hv,
    
    admit,

    admit,
end

theorem exists_normalised_basis : 
∃ (b : set V), is_basis b ∧ ∀ (x : V), x ∈ b → is_normalised x :=
begin
have H1 : ∃ (b : set V), is_basis b,
    exact exists_is_basis V,
apply exists.elim H1,
intros b Hb,
exact exists.intro (normalise_set b) (and.intro (normalised_basis_is_basis b Hb) (normalise_set_normalises b (zero_not_mem_of_linear_independent (zero_ne_one ℂ) Hb.left))),
end

noncomputable instance complex_is_norm_space : norm_space ℂ :=
{
N := abs,
norm_nonneg := abs_nonneg,
norm_sub_add := by exact abs_add,
norm_abs_hom := by simp,
norm_pos_def := by simp; exact abs_eq_zero,
}
