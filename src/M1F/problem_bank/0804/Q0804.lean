import data.real.basic

--\medskip\noindent{\bf Q0804.} For each of the following binary relations on a set~$S$,
-- figure out whether or not the relation is reflexive. Then figure out whether or not
--  it is symmetric. Finally figure out whether or not the relation is transitive.

inductive S5
| one : S5
| two : S5
| three : S5
| four : S5

inductive S6.

open S5

definition r1 (a b : ℝ) : Prop := a ≤ b
definition r2 (a b : ℤ) : Prop := ∃ k, a - b = k ^ 2
definition r3 (a b : ℝ) : Prop := a = b ^ 2
definition r4 (a b : ℤ) : Prop := a + b = 0
definition r5 (a b : S5) : Prop := a = one ∧ b = three
definition r6 (a b : S6) : Prop := true

theorem Q1r : reflexive r1 := sorry
theorem Q1r : ¬ (reflexive r1) := sorry

theorem Q4r : transitive r4 := sorry
theorem Q4r : ¬ (transitive r4) := sorry
