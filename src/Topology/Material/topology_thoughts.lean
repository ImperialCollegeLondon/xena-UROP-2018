import analysis.metric_space
import tactic.norm_num


local attribute [instance, priority 0] classical.prop_decidable
noncomputable theory

def discrete_metric_space' (α : Type*) : metric_space α :=
{
    dist := λ a b, if a = b then 0 else 1,
    dist_self := begin intro x, unfold ite,
        rw eq_true_intro (eq.refl x), exact if_true 0 1,
        end,
    eq_of_dist_eq_zero := begin intros x y, dsimp, split_ifs,
      intro _,exact h,
      norm_num,
        end,
    dist_comm := begin intros x y, dsimp,
      split_ifs,
        refl,
        cases (h_1 h.symm),
        cases (h h_1.symm),
        refl
        end,
    dist_triangle := begin
      intros, dsimp, split_ifs,
        right,refl,
        left,show (0 : ℝ) < 0 + 1,norm_num,
        left,show (0 : ℝ) < 1 + 0,norm_num,
        left,show (0 : ℝ) < 1 + 1,norm_num,
        exfalso,apply h,rwa h_1,
        right,refl,
        right,refl,
        left, show (1 : ℝ) < 1 + 1, norm_num,
    end
}