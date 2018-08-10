import algebra.module linear_algebra.basic analysis.real data.vector data.list.basic

universes u

-- def R_n_basis (n : nat) : set (vector ℝ n) :=
-- {v | ∀ i : fin n, (v.nth i = 1 ∧ ∀ j : fin n, j.val ≠ i.val → v.nth j = 0) }

namespace vector

variables {n : ℕ} {R : Type u } [h : ring R]

include n R h

instance : module R (vector R n) :=
{
    add := map₂ h.add,
    add_assoc := by 
        { intros a b c, simp,
        cases a with a la,
        cases b with b lb,
        cases c with c lc,
        unfold map₂, simp,
        induction n with n ih generalizing a b c,
            { cases a; cases c,
            rw [list.nil_map₂, list.map₂_nil, list.nil_map₂],
            repeat { contradiction } },
            { cases a, contradiction,
                cases b, contradiction,
                cases c, contradiction,
                unfold list.map₂,
                simp [nat.add_one] at la lb lc,
                apply congr, 
                    { apply congr, refl, apply add_assoc },
                    exact ih _ _ _ la lb lc } },
    add_comm := by 
        { intros a b, simp [has_add.add], 
        cases a with a la,
        cases b with b lb,
        unfold map₂, simp,
        induction n with n ih generalizing a b,
            { cases a; cases b, 
            unfold list.map₂, repeat { contradiction } },
            { cases a, contradiction,
                cases b, contradiction,
                unfold list.map₂, 
                simp [nat.add_one] at la lb,
                apply congr,
                    { apply congr, refl, apply add_comm },
                    exact ih _ _ la lb } },
    zero := @repeat R 0 n,
    zero_add := by 
        { intro a, simp,
        cases a with a la, 
        unfold repeat map₂, simp,
        induction n with n ih generalizing a; 
        unfold list.repeat; cases a,
            apply list.map₂_nil,
            repeat { contradiction }, 
            unfold list.map₂,
            simp [nat.add_one] at la,  
            apply congr,
                { apply congr, refl, apply zero_add},
                exact ih _ la },
    add_zero := by 
        { intro a, simp [has_add.add],
        cases a with a la,
        unfold repeat map₂, simp,
        induction n with n ih generalizing a;
        unfold list.repeat; cases a,
            apply list.map₂_nil,
            repeat { contradiction },
            unfold list.map₂,
            simp [nat.add_one] at la,
            apply congr,
                { apply congr, refl, apply add_zero },
                exact ih _ la },
    smul := map ∘ h.mul,
    smul_add := by 
        { intros r a b, simp [add_group.add],
        cases a with a la,
        cases b with b lb,
        unfold map map₂, simp,
        induction n with n ih generalizing a b,
            { cases a; cases b,
            rw [list.map, list.map₂_nil, list.map], 
            repeat { contradiction } },
            { cases a, contradiction,
            cases b, contradiction,
            unfold list.map list.map₂,
            simp [nat.add_one] at la lb,
            apply congr, 
                { apply congr, refl, apply left_distrib },
                exact ih _ _ la lb } },
    add_smul := by 
        { intros r s a, 
        simp [has_add.add, add_semigroup.add, 
            add_monoid.add, add_group.add],
        cases a with a la,
        unfold map map₂, simp,
        induction n with n ih generalizing a;
        cases a; unfold list.map list.map₂,
            repeat { contradiction },
            simp, split, 
            apply right_distrib,
            simp [nat.add_one] at la,
            exact ih _ la },
    mul_smul := by  
        { intros r s a, simp,
        cases a with a la,
        unfold map, simp,
        induction n with n ih generalizing a;
        cases a; unfold list.map,
            repeat { contradiction },
            simp, split, 
            apply mul_assoc,
            simp [nat.add_one] at la,
            exact ih _ la },
    one_smul := by 
        { intro a, simp,
        cases a with a la,
        unfold map, simp,
        induction n with n ih generalizing a;
        cases a; unfold list.map,
            repeat { contradiction }, 
            simp, split, 
            apply h.one_mul,
            simp [nat.add_one] at la,
            exact ih _ la },
    neg := map h.neg,
    add_left_neg := by
        { intro a, simp,
        simp [has_zero.zero],
        unfold repeat,
        cases a with a la,
        unfold map map₂, simp,
        induction n with n ih generalizing a;
        unfold list.repeat; cases a; simp,
            repeat { contradiction },
            split, 
            apply add_left_neg,
            simp [nat.add_one] at la,
            exact ih _ la } 
}

instance [field R] : vector_space R (vector R n) :=
sorry

end vector
