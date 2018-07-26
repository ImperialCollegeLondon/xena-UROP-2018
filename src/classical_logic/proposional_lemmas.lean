open classical

variables { p q r : Prop }

theorem not_not_iff : ¬¬p ↔ p :=
by { split; intro h, 
    { apply by_contradiction, intro h1, exact h h1 },
    exact not_not_intro h }

theorem imp_classical : p → q ↔ ¬ p ∨ q := 
by { split; intro h,
    { apply @by_cases p; intro h1,
         { right, exact h h1 }, { left, exact h1 } },
    { intro h1, cases h with h h, exact absurd h1 h, exact h } }

theorem not_and_iff_neg_or : ¬ (p ∧ q) ↔ (¬ p ∨ ¬ q) :=
by { split; intro h,
    { apply @by_cases p; intro h1,
        { apply @by_cases q; intro h2,
            { apply false.elim, apply h,
                split, exact h1, exact h2 },
            { right, exact h2 } },
        { left, exact h1 } },
    { intro h1, cases h1 with h2 h3, cases h with h h; apply h,
        exact h2, exact h3 } }

theorem not_or_iff_neg_and : ¬ (p ∨ q) ↔ (¬ p ∧ ¬ q) :=
by { split; intro h, 
    { split; intro h1; apply h,
        { left, exact h1 }, { right, exact h1 } },
    { cases h with h h1, intro h2, cases h2 with h2 h2,
        { apply h, exact h2 }, { apply h1, exact h2 } } }