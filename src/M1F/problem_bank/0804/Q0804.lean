import data.real.basic

--\medskip\noindent{\bf Q0804.} For each of the following binary relations on a set~$S$,
-- figure out whether or not the relation is reflexive. Then figure out whether or not
--  it is symmetric. Finally figure out whether or not the relation is transitive.

definition S5 := {x : ℕ | x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4}
definition S6 := {x : ℕ | false}

definition r1 (a b : ℝ) : Prop := a ≤ b
definition r2 (a b : ℤ) : Prop := ∃ k, a - b = k ^ 2
definition r3 (a b : ℝ) : Prop := a = b ^ 2
definition r4 (a b : ℤ) : Prop := a + b = 0
definition r5 (a b : S5) : Prop := a = 1 ∧ b = 3
definition r6 (a b : S6) : Prop := true

theorem Q1r : reflexive r1 := sorry
theorem Q1r : ¬ (reflexive r1) := sorry

theorem Q4r : transitive r4 := sorry
theorem Q4r : ¬ (transitive r4) := sorry
