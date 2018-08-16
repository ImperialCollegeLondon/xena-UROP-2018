import algebra.big_operators algebra.group_power data.pnat M3P14.Arithmetic_functions.phi

-- positive naturals
-- todo: add all the properties of dirichlet conv

namespace nat

open list

/-- returns the finset of divisors of a positive natural -/
definition factors_new (d : ℕ+) : list ℕ := 
  filter (λ e, e ∣ d) (range (d+1))

#eval factors_new 6 -- [1, 2, 3, 6]

lemma mem_factors_iff_divides (d : ℕ+) (e : ℕ) : e ∈ factors_new d ↔ e ∣ d :=
begin
  unfold factors_new,
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

lemma nodup_factors (d : ℕ+) : nodup (factors_new d) :=
nodup_filter _ (nodup_range (d+1) : nodup (range (d+1)))

/-- returns the sum of f(e) as e ranges over the divisors of d (positive nat) -/
definition divisor_sum 
  {β : Type*} [add_comm_monoid β] (f : ℕ → β) (d : ℕ+) : β := 
finset.sum (⟨quotient.mk (factors_new d),nodup_factors d⟩) f

def perfect_num (n : ℕ+) : Prop :=  divisor_sum id n = 2*n

--theorem perfect_number_iff_mersenne (n p: ℕ+) (hp: prime p) : perfect_num n ↔ n = 2^(p-1)*((2^p)-1)

instance : decidable_pred perfect_num := λ _, by unfold perfect_num; apply_instance

theorem divisor_sum_phi (n : ℕ+) : divisor_sum (phi) n = n := sorry 

#eval divisor_sum (id) (6) -- it's a perfect number!
#reduce (perfect_num 6 : bool)
#eval (perfect_num 5 : bool)

--dirichlet convolution
def conv (f : ℕ → ℕ) (g : ℕ → ℕ) := λ (n : pnat), divisor_sum (λ d, f d * g (n / d)) n

--#eval conv phi id

-- lemmas about conv

lemma conv_is_comm (f g : ℕ → ℕ) : conv f g = conv g f := sorry

--lemma conv_is_assoc (f g h : ℕ → ℕ) : conv (conv f g) h = conv f (conv g h) := sorry

--lemma conv_is_add_dist (f g h : ℕ → ℕ) : conv f (g + h) = conv f g + conv f h

--lemma conv_id_is_conv (f : ℕ → ℕ) : conv f id = f := sorry

--lemma conv_mul_is_mul (f g : ℕ → ℕ) : is_mult f 

--lemma conv_has_inv (f : ℕ → ℕ) (hp : f 1 ≠ 0) : ∃ g : conv f g = id := sorry
end nat 
