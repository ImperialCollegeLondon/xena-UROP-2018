import algebra.module linear_algebra.basic analysis.real data.vector data.list.basic

universes u w

def R_n_basis (n : nat) : set (vector ℝ n) :=
{v | ∀ i : fin n, (v.nth i = 1 ∧ ∀ j : fin n, j.val ≠ i.val → v.nth j = 0) }

namespace vector

variables {n : ℕ}

include n

-- def has_scalar : has_scalar ℝ (vector ℝ n) :=
-- { smul := map ∘ real.has_mul.mul }

-- def has_scalar.smul := @has_scalar.smul ℝ _ (@has_scalar n)

-- infix ` • ` := has_scalar.smul

-- def has_add : has_add (vector ℝ n) := 
-- { add := map₂ real.has_add.add }

-- def has_add.add := @has_add.add _ (@has_add n)

-- infix ` + ` := has_add.add

-- def has_zero : has_zero (vector ℝ n) :=
-- { zero := repeat 0 n }

-- def has_zero.zero := @has_zero.zero _ (@vector.has_zero n)

-- notation 0 := vector.has_zero.zero

set_option pp.all false
-- set_option pp.all true

-- variables (a b : vector ℝ n)

instance : add_comm_group (vector ℝ n) :=
{
    add := map₂ real.has_add.add,
    add_assoc := by 
        { simp, intros a b c,
         },
    zero := @repeat ℝ 0 n,
    neg := (map ∘ real.has_mul.mul) (-1),
    add_left_neg := by simp ,
    zero_add := by 
        { simp, intro a,
        apply vector.eq, unfold to_list,
        cases a with a la, 
        unfold repeat map₂, simp,
        induction n with n ih generalizing a; unfold list.repeat,
            { cases a,
            apply list.map₂_nil,
            contradiction }, 
            { cases a with ha ta,
            contradiction,
            unfold list.map₂,
            rw [zero_add],
            
             } } },
}
#check list.map₂ 
noncomputable instance : vector_space ℝ (vector ℝ n) :=
{ 
    smul := vector.map ∘ real.has_mul.mul,
    smul_add := λ r x y, by {},
}

end vector

-- #reduce (vector ℝ 3)
#print module
#check list.map₂_nil
#check iff