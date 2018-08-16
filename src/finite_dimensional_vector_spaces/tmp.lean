import finite_dimensional_vector_spaces.ring_n_is_module

universes u

namespace fin_dim_ring

variables (R : Type u) [h : ring R] (n : ℕ)

-- structure fin_dim_ring extends module R (vector R n)

include h 

def elemental_vector (i : fin n) : vector R n :=
vector.of_fn (λ j, if (j.val = i.val) then 1 else 0)
-- match n, i with
-- | 0, _ := vector.nil
-- | (n+1), ⟨0, _⟩ := vector.cons 1 (vector.repeat 0 n)
-- | (n+1), ⟨i+1, l⟩ := vector.cons 0 
--     $ by exact _match _ ⟨_, (nat.lt_of_succ_lt_succ l)⟩
-- end

def basis : vector (vector R n) n :=
vector.of_fn (elemental_vector R n)

-- noncomputable def basis_as_finset : finset (vector R n) :=
-- by {
--     apply @multiset.to_finset _ _,
--     exact (basis R n).to_list,
--     exact classical.dec_eq _
-- }

def basis_as_finset : finset (vector R n) :=
{
    val := (basis R n).to_list,
    nodup := by 
        { 
        rw [multiset.coe_nodup],
        unfold basis list.nodup,
        rw [vector.to_list_of_fn],
        unfold list.of_fn,
        -- simp [basis, list.nodup, list.of_fn],
        induction n with n ih,
        unfold list.of_fn_aux,
        
         }
}

#check list.pairwise

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

end fin_dim_ring 