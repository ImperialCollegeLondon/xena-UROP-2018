import analysis.metric_space algebra.module inner_product_spaces.basic
universes u v
variables V W : Type

section norm_space

-- Banach space is a complete normed space.
class banach_space (V : Type) extends norm_space V: Type :=
(complete: complete_space ℝ)

variables (v : Type) [norm_space V]
def norm : V → ℝ := norm_space.N

#check @eq.trans 
-- Incorrect, working on it atm
noncomputable lemma banach_is_metric [h : banach_space V] : metric_space V :=
{
dist := by {
    intros x y,
    have n := h.N,
    exact n (x - y) },
dist_self := by { 
    intro,
    have d := h.norm_pos_def,
    rw [sub_self],
    apply (d (0 : V)).mpr,
    exact eq.refl (0 : V) },
eq_of_dist_eq_zero := by {
    intros x y hxy,
    have d := h.norm_pos_def,
    replace d := (d (x - y)).mp hxy,
    replace d := congr_arg (+ y) d,
    simp at d,
    have a := add_zero y,
    exact eq.trans d a },
dist_comm := 
    begin
    intros,
    dunfold herm_dist, 
    dunfold herm_norm,
    rw sqrt_inj (is_pos_def (x - y)).left (is_pos_def (y - x)).left,
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

end norm_space
-- theorem completion 
