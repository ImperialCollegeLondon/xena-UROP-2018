import algebra.module linear_algebra.basic analysis.real

universes u w

-- variables {k : Type u} [field k] {V : Type w} 

-- instance fvs {n : nat} (B : set (vector k n)) 
--     [@is_basis k (vector k n) _ {} B] : vector_space k V := 
-- by constructor 

def R_n_basis (n : nat) : set (vector ℝ n) :=
{v | ∀ i : fin n, (v.nth i = 1 ∧ ∀ j : fin n, j.val ≠ i.val → v.nth j = 0) }

section vector

variables {n : ℕ}

instance vector.has_scalar : has_scalar ℝ (vector ℝ n) :=
{ smul := vector.map ∘ real.has_mul.mul }

instance vector.has_add : has_add (vector ℝ n) := 
{ add := vector.map₂ real.has_add.add }

-- instance : add_semigroup (vector ℝ n) :=
-- { 
--     add := vector.has_add.add,
--     add_assoc := by }

instance vector.has_zero : has_zero (vector ℝ n) :=
{ zero := vector.repeat (0 : ℝ) n }

-- set_option pp.all false

instance : add_comm_group (vector ℝ n) :=
{
    add := vector.has_add.add,
    add_assoc := by 
        { intros a b c,  
        apply vector.eq,
        have lhs := vector.to_list (a+b+c),
        have := lhs.cases_on,
        },
    zero := vector.has_zero.zero,
    zero_add := by 
        { intro a, 
        cases n,
        have := vector.map_nil, },
}

noncomputable instance : vector_space ℝ (vector ℝ n) :=
{ 
    smul := vector.map ∘ real.has_mul.mul,
    smul_add := λ r x y, by {},
}

end vector

-- #reduce (vector ℝ 3)
#print module
#check vector.add_comm_group
#check list.unzip
#check iff