import finite_dimensional_vector_spaces.ring_n_is_module

universes u


def matrix_space (m n : ℕ) (R :  Type u) 
    [h : ring R] := vector R n → vector R m

namespace fin_dim_ring

variables (R : Type u) [h : ring R] (n : ℕ)


-- structure fin_dim_ring extends module R (vector R n)
include h 

def elemental_vector (i : fin n) : vector R n :=
-- vector.of_fn (λ j, if (j = i) then 1 else 0)
match n with
| 0, _ := vector.nil
| (n+1), ⟨0, _⟩ := vector.cons 1 (vector.repeat 0 n)
| (n+1), ⟨i+1, l⟩ := vector.cons 0 
    $ by exact _match _ ⟨_, (nat.lt_of_succ_lt_succ l)⟩
end

def basis : vector (vector R n) n :=
vector.of_fn (elemental_vector R n)

-- def basis_as_finset : finset (vector R n) :=
-- by {
--     have := @multiset.to_finset,
-- }

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