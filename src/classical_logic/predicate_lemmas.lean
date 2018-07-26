open classical

variables { α : Type } { p q : α → Prop }
variable { a : α }
variable { r: Prop }


theorem not_all_iff_ex_not : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
by { split; intro h,
    { apply by_contradiction, intro h1, apply h,
        intro h2, apply by_contradiction, intro h3, 
        apply h1, split, exact h3 },
    { intro h1, cases h with h2 h3, exact h3 (h1 h2) } }

theorem not_ex_iff_all_not : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
by { split; intro h,
    { intros _ h1, apply h, split, exact h1 },
    { intro h1, cases h1 with h2 h3, exact h h2 h3 } }

theorem not_all_not_iff_ex : (¬ ∀ x, ¬ p x) ↔ (∃ x, p x) :=
by { split; intro h,
    { apply by_contradiction, intro h1, apply h,
        intros _ h2, apply h1, split, exact h2 },
    { intro h1, cases h with h h2, exact h1 h h2 } }

theorem not_ex_not_iff_all : (¬ ∃ x, ¬ p x) ↔ (∀ x, p x) :=
by { split; intros h h1,
    { apply by_contradiction, intro h2, 
        apply h, split, exact h2 },
    { cases h1 with h1 h2, exact h2 (h h1) } }

theorem all_and_iff_and_all : 
    (∀ x, p x ∧ q x) ↔ ((∀ x, p x) ∧ (∀ x, q x)) :=
by { split; intro h,
    { split; intro h1, exact (h h1).left, exact (h h1).right },
    { intro, split, apply h.left, apply h.right } }

theorem ex_or_iff_or_ex : 
    (∃ x, (p x ∨ q x)) ↔ ((∃ x, p x) ∨ (∃ x, q x)) :=
by { split; intro h,
    { cases h with _ h, cases h with h h,
        { left, constructor, exact h },
        { right, constructor, exact h } },
    { cases h with h h; cases h with _ h; constructor,
        { left, exact h }, { right, exact h } } }

theorem ex_and_reduce : (∃ x, r ∧ p x) ↔ (r ∧ ∃ x, p x) :=
by { split; intro h,
    { cases h with _ h, split, exact h.left, 
        { split, exact h.right } },
    { cases h with h h1, cases h1 with h1 h2, 
        existsi h1, split, exact h, exact h2 } }

theorem all_or_reduce : (∀ x, r ∨ p x) ↔ (r ∨ ∀ x, p x) :=
by { split; intro h,
    { apply @by_cases r; intro h1,
        { left, exact h1 },
        { right, intro h2, cases (h h2) with h h, 
            exact absurd h h1, exact h } },
    { intro h1, cases h with h h,
        { left, exact h }, { right, exact h h1 } } }

theorem all_mp_reduce_all : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
by { split; intros h h1 h2; exact h h2 h1 }

theorem all_mpr_reduce_ex : (∀ x, p x → r) ↔ ((∃ x, p x) → r) :=
by { split; intro h,
    { intro h1, cases h1 with h1 h2, exact h h1 h2 },
    { intros h1 h2, apply h, split, exact h2 } }

include a
theorem all_not_free_reduce : (∀ x : α, r) ↔ r :=
by { split; intro h, exact h a, { intro, exact h } }

theorem ex_not_free_reduce : (∃ x : α, r) ↔ r :=
by { split; intro h, 
    { cases h with _ h, exact h}, 
    { existsi a, exact h } }

theorem ex_mp_reduce_ex : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
by { split; intro h,
    { intro h1, cases h with h h2, existsi h, exact h2 h1},
    { apply @by_cases r; intro h1,
        { cases (h h1) with _ h, split, intro, exact h },
        { existsi a, intro h2, exact absurd h2 h1 } } }

theorem ex_mpr_reduce_all : (∃ x, p x → r) ↔ ((∀ x, p x) → r) :=
by { split; intro h,
    { intro h1, cases h with h h2, exact h2 (h1 h) },
    { apply @by_cases (∀ (x : α), p x); intro h1,
        { existsi a, intro, exact h h1 },
        { have h2 := not_all_iff_ex_not.mp h1, cases h2 with h2 h3,  
            existsi h2, intro h4, exact absurd h4 h3 } } }
omit a