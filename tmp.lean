import analysis.real
import algebra.module
import linear_algebra.basic

example (p : Prop) (h : p → ℕ) (k : ¬ p → ℕ) : ℕ :=
by { have : p ∨ ¬ p → ℕ,
    { intro h, have n := h.elim, } }