-- sums over sets
import algebra.big_operators

-- positive naturals
import data.pnat 

namespace nat

open list

/-- returns the finset of divisors of a positive natural -/
definition factors (d : ℕ+) : list ℕ := 
  filter (λ e, e ∣ d) (range (d+1))

#eval factors 6 -- [1, 2, 3, 6]

lemma mem_factors_iff_divides (d : ℕ+) (e : ℕ) : e ∈ factors d ↔ e ∣ d :=
begin
  unfold factors,
  rw mem_filter,
  split,
  { -- easy direction
    intro H, exact H.2
  },
  { -- this is the "hard direction" :-)
    intro H,
    have He_le_d : e ≤ ↑d := le_of_dvd d.property H,
    split,
      rw mem_range,
      exact lt_of_le_of_lt He_le_d (lt_succ_self _),
    exact H
  }
end

lemma nodup_factors (d : ℕ+) : nodup (factors d) :=
nodup_filter _ (nodup_range (d+1) : nodup (range (d+1)))

/-- returns the sum of f(e) as e ranges over the divisors of d (positive nat) -/
definition divisor_sum 
  {β : Type*} [add_comm_monoid β] (f : ℕ → β) (d : ℕ+) : β := 
finset.sum (⟨quotient.mk (factors d),nodup_factors d⟩) f

end nat 

open nat

#eval divisor_sum (id) (6) -- it's a perfect number!