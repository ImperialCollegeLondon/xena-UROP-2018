-- real numbers
import data.real.basic

-- useful lemmas
import xenalib.M1F.Q0107
noncomputable theory

def A : set ℝ := { x | x^2 < 3}
def B : set ℝ := { x | x^2 < 3 ∧ ∃ y : ℤ, x = y}
def C : set ℝ := { x | x^3 < 3}

definition real_half := (1 / 2 : ℝ)
-- useful lemmas

#check (B_is_minus_one_zero_one : ∀ (x : ℝ), x ∈ B ↔ x = -1 ∨ x = 0 ∨ x = 1)
#check (real_half_not_in_B : real_half ∉ B)

-- For each part x, prove exactly one of part_x_true and
-- part_x_false, and comment out the other one!

theorem part_a_true : (1/2 : ℝ) ∈ A ∩ B := sorry
theorem part_a_false : ¬ (1/2 : ℝ) ∈ A ∩ B := sorry
theorem part_b_true : (1/2 : ℝ) ∈ A ∪ B := sorry
theorem part_b_false : ¬ (1/2 : ℝ) ∈ A ∪ B := sorry
theorem part_c_true : A ⊆ C := sorry
theorem part_c_false : ¬ A ⊆ C := sorry
theorem part_d_true : B ⊆ C := sorry
theorem part_d_false : ¬ B ⊆ C := sorry
theorem part_e_true : C ⊆ A ∪ B := sorry
theorem part_e_false : ¬ C ⊆ A ∪ B := sorry
theorem part_f_true : (A ∩ B) ∪ C = (A ∪ B) ∩ C := sorry
theorem part_f_false : ¬ (A ∩ B) ∪ C = (A ∪ B) ∩ C := sorry
