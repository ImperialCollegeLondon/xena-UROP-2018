import algebra.module linear_algebra.basic analysis.real data.vector data.list.basic

universes u

-- def R_n_basis (n : nat) : set (vector ℝ n) :=
-- {v | ∀ i : fin n, (v.nth i = 1 ∧ ∀ j : fin n, j.val ≠ i.val → v.nth j = 0) }

namespace vector

variables {n : ℕ} {R : Type u }

instance [h : ring R]: module R (vector R n) :=
{
    add := map₂ h.add,
    add_assoc := by 
        { intros a b c,
        cases a with a la,
        cases b with b lb,
        cases c with c lc,
        simp [map₂],
        induction n with _ ih generalizing a b c;
        cases a; cases b; cases c; simp [list.map₂],
            contradiction,
            simp [nat.add_one] at la lb lc,
            split, apply add_assoc, exact ih _ _ _ la lb lc },
    add_comm := by 
        { intros a b, 
        cases a with a la,
        cases b with b lb,
        simp [has_add.add, map₂],
        induction n with _ ih generalizing a b;
        cases a; cases b; simp [list.map₂], 
            contradiction,
            simp [nat.add_one] at la lb,
            split, apply add_comm, exact ih _ _ la lb },
    zero := repeat h.zero _,
    zero_add := by 
        { intro a,
        cases a with a la, 
        simp [repeat, map₂],
        induction n with _ ih generalizing a; 
        cases a; simp [list.repeat, list.map₂],
            contradiction,
            simp [nat.add_one] at la,  
            split, apply zero_add, exact ih _ la },
    add_zero := by 
        { intro a, 
        cases a with a la,
        simp [has_add.add, repeat, map₂],
        induction n with _ ih generalizing a;
        cases a; simp [list.repeat, list.map₂],
            contradiction,
            simp [nat.add_one] at la,
            split, apply add_zero, exact ih _ la },
    smul := map ∘ h.mul,
    smul_add := by 
        { intros _ a b,
        cases a with a la,
        cases b with b lb,
        simp [add_group.add, map, map₂],
        induction n with _ ih generalizing a b; 
        cases a; cases b; simp [list.map, list.map₂],
            contradiction,
            simp [nat.add_one] at la lb,
            split, apply left_distrib, exact ih _ _ la lb },
    add_smul := by 
        { intros _ _ a, 
        cases a with a la,
        simp [has_add.add, add_semigroup.add,
            add_monoid.add, add_group.add, map, map₂],
        induction n with _ ih generalizing a; 
        cases a; simp [list.map, list.map₂],
            contradiction,
            simp [nat.add_one] at la,
            split, apply right_distrib, exact ih _ la },
    mul_smul := by  
        { intros _ _ a, 
        cases a with a la,
        simp [map],
        induction n with _ ih generalizing a; 
        cases a; simp [list.map],
            contradiction,
            simp [nat.add_one] at la,
            split, apply mul_assoc, exact ih _ la },
    one_smul := by 
        { intro a, 
        cases a with a la,
        simp [map],
        induction n with _ ih generalizing a; 
        cases a; simp [list.map], 
            contradiction,
            simp [nat.add_one] at la,
            split, apply one_mul, exact ih _ la },
    neg := map h.neg,
    add_left_neg := by
        { intro a, 
        cases a with a la,
        simp [repeat, map, map₂],
        induction n with _ ih generalizing a; 
        cases a; simp [list.repeat, list.map, list.map₂],
            repeat { contradiction },
            simp [nat.add_one] at la,
            split, apply add_left_neg,
                exact ih _ la } 
}

instance [h : field R] : vector_space R (vector R n) := 
vector_space.mk _ _

end vector