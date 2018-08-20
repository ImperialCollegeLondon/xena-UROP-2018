import finite_dimensional_vector_spaces.ring_n_is_module

universes u

namespace fin_vector_space

variables (R : Type u) [h : field R] (n : ℕ)

-- structure fin_dim_ring extends module R (vector R n)

include h 

def elemental_vector (i : fin n) : vector R n :=
-- vector.of_fn (λ j, @decidable.by_cases (j = i) R _ (λ _, 1) (λ _, 0))
-- vector.of_fn (λ j, if (j.val = i.val) then 1 else 0)
match n, i with
| 0, _ := vector.nil
| (n+1), ⟨0, _⟩ := vector.cons 1 (vector.repeat 0 n)
| (n+1), ⟨i+1, l⟩ := vector.cons 0 
    $ by exact _match _ ⟨_, (nat.lt_of_succ_lt_succ l)⟩
end

def basis : vector (vector R n) n :=
vector.of_fn (elemental_vector R n)

def basis_as_finset : finset (vector R n) :=
{
    val := (basis R n).to_list,
    nodup := by 
        { rw [basis, vector.to_list_of_fn, 
            multiset.coe_nodup, list.nodup_iff_nth_le_inj],
        intros i j h1 h2,
        rw [list.length_of_fn] at h1 h2,
        rw [list.nth_le_of_fn (elemental_vector R n) ⟨i, h1⟩,
            list.nth_le_of_fn (elemental_vector R n) ⟨j, h2⟩],
        intro a,
        induction n with n ih generalizing i j,
        exact (nat.le_lt_antisymm (i.zero_le) h1).elim,
        cases i; cases j; unfold elemental_vector at a,
            { replace a := @congr _ _ (vector.head) _ _ _ rfl a,
            rw [vector.head_cons, vector.head_cons] at a,
            by_contradiction, 
            apply (not_not_intro a),
            exact h.zero_ne_one.symm },
            { replace a := @congr _ _ (vector.head) _ _ _ rfl a,
            rw [vector.head_cons, vector.head_cons] at a,
            by_contradiction, 
            apply (not_not_intro a),
            exact h.zero_ne_one },
            { rw [list.length_of_fn] at ih,
            have hi := nat.lt_of_succ_lt_succ h1_1,
            have hj := nat.lt_of_succ_lt_succ h2_1,
            apply congr rfl,
            apply ih _ _ hi hj hj hi,
            replace a := @congr _ _ (vector.tail) _ _ _ rfl a,
            rw [vector.tail_cons, vector.tail_cons] at a,
            exact a } }
}

#check nat.lt_of_add_lt_add_left

-- def lc_basis : lc R (vector R n) :=
-- by { split, swap, 
--     exact basis_as_finset R n,
--     swap, intro v,

--      }

-- #check finset

-- instance : is_basis (basis_as_finset R n).to_set :=
-- by { split, swap,
--         { intro v,
--         split, swap,
--         unfold lc, split,
--         swap, exact basis_as_finset R n,
--         swap, 
--          }
-- }

-- instance : is_basis { v | v ∈ (basis R n).to_list } := 
-- by { split,
--     { --simp [linear_independent],
--     unfold linear_independent basis,
--     intros l h1 h2, simp at h1,
--     simp [vector.eq_nil 0, finsupp.sum] at h2,
--     -- induction n with _ ih generalizing l,
--     cases l with ls lf lh,
--     simp [list.of_fn, list.of_fn_aux] at h1,
--     simp [coe_fn, has_coe_to_fun.coe] at h1 h2,
--     simp [has_zero.zero],
--     simp [has_zero.zero, add_monoid.zero, add_group.zero, 
--         add_comm_group.zero, vector.repeat] at h2,
--     cases ls with lsv lss,
--     split,
--     induction n with _ ih,
    
--      }, }

end fin_vector_space