import algebra.module linear_algebra.basic analysis.real data.vector data.list.basic

universes u

namespace vector

variables (n : ℕ) (R : Type u)

instance to_module [h : ring R] : module R (vector R n) :=
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
            split, apply add_left_neg, exact ih _ la } 
}

instance to_vector_space [h : field R] : vector_space R (vector R n) := 
vector_space.mk _ _

instance [h : ring R] : has_add (vector R n) := by apply_instance

end vector

def matrix_space (m n : ℕ) (R :  Type u) 
    [h : ring R] := vector R n → vector R m

namespace fin_dim_ring

variables (R : Type u) [h : ring R] (n : ℕ)


-- structure fin_dim_ring extends module R (vector R n)
include h 

example : module R (vector R n) := by apply_instance

def elemental_vector (i : fin n) : vector R n :=
-- match n, i with
-- | 0, _ := vector.nil
-- | (n+1), ⟨0, _⟩ := vector.cons 1 (vector.repeat 0 n)
-- | (n+1), ⟨i+1, l⟩ := vector.cons 0 
--     $ by exact _match n ⟨i, (nat.lt_of_succ_lt_succ l)⟩
-- end
vector.of_fn $ (λ j, if (i = j) then 1 else 0)

#check @list.pairwise
#check @list.of_fn_aux

def basis : vector (vector R n) n :=
vector.of_fn (elemental_vector R n)
 
#check basis

-- set_option pp.all true


-- lemma is_spanning_set : ∀ (x : vector R n), 
--     x ∈ span {v : vector R n | v ∈ vector.to_list (basis R n)} :=
-- by { intro a,
--     unfold span basis,
--     split, swap,
--     unfold lc, 
--     apply @finsupp.mk (vector R n) R,
--         { intro v, }
-- }

#check list.nodup_decidable
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

end fin_dim_ring 