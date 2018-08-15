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
by simp [factors, -add_comm, nat.lt_succ_iff];
   exact and_iff_right_of_imp (le_of_dvd d.2)

lemma nodup_factors (d : ℕ+) : nodup (factors d) :=
nodup_filter _ (nodup_range (d+1) : nodup (range (d+1)))

/-- returns the sum of f(e) as e ranges over the divisors of d (positive nat) -/
definition divisor_sum 
  {β : Type*} [add_comm_monoid β] (f : ℕ → β) (d : ℕ+) : β := 
finset.sum (⟨quotient.mk (factors d),nodup_factors d⟩) f

end nat 

open nat

#eval divisor_sum (id) (6) -- it's a perfect number!