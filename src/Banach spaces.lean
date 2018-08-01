import analysis.metric_space algebra.module inner_product_spaces.basic
universes u v
variables V W : Type

section norm_space

-- Banach space is a complete normed space.
class banach_space (V : Type) extends norm_space V: Type :=
(complete: complete_space ℝ)

noncomputable lemma banach_is_metric [h : banach_space V] : metric_space V :=
{
dist := by {
    intros x y,
    have n := h.N,
    exact n (x - y) },
dist_self := by {
    have d := h.norm_pos_def,
    intro,
    rw [sub_self],
    apply (d 0).mpr, 
    refl },
eq_of_dist_eq_zero := by {
    have d := h.norm_pos_def,
    intros x y hxy,
    replace d := (d (x - y)).mp hxy,
    replace d := congr_arg (+ y) d,
    simp at d, exact d },
dist_comm := by {
    have d := h.norm_abs_hom,
    intros x y,
    replace d := d (y - x) (-1), 
    simp at d, exact d },
dist_triangle := by {
    have d := h.norm_sub_add,
    intros x y z,
    replace d := d (x - y) (y - z),
    simp at d, exact d },
}

end norm_space
-- theorem completion 
