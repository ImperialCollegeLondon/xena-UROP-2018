open classical

variables { p q r : Prop }

theorem not_not_iff : ¬¬p ↔ p :=
⟨by_contradiction ∘ flip absurd, not_not_intro⟩ 

theorem imp_classical : p → q ↔ ¬ p ∨ q := 
⟨λh, by_cases (or.inr ∘ h) or.inl, λh h1, h.elim (absurd h1) id⟩

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