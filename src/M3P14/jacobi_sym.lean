import data.nat.basic M3P14.order_zmodn_kmb data.int.basic M3P14.lqr

private theorem aux1 (a b : ℕ) (h : ¬a + 3 = b + 1) : 
    b + 1 ≠ a + 3 := 
begin
    suffices : b + 1 = a + 3 → false, by simp [this],
    intro h2,
    exact absurd h2.symm h,
end

private theorem aux2 (a b : ℕ) (h : a + 3 ≥ int.nat_abs ↑(nat.succ b)) : 
    (a + 3) % (nat.succ b) < nat.succ (nat.succ (nat.succ a)) := 
begin
    simp at h,
    suffices : (a + 3) % (b + 1) < (a + 3), by simp [this],
    cases (classical.em (a + 3 = b + 1)),
    rw [h_1.symm, nat.mod_self],
    exact dec_trivial,
    have eq : int.nat_abs (1 + ↑b) = 1 + b, from int.nat_abs_of_nat (1 + b),
    have h2 : a + 3 ≥ b + 1, rw eq at h, rwa add_comm b 1,
    suffices : (nat.succ b) < nat.succ (nat.succ (nat.succ a)), from lt_trans (nat.mod_lt (a + 3) (nat.pos_iff_ne_zero.mpr (by trivial))) this,
    suffices : b + 1 < a + 3, by simp [this],
    suffices : b + 1 ≤ a + 3, from lt_of_le_of_ne this (aux1 a b h_1),
    exact h2,
end

private theorem aux3 (a b : ℕ) (h : ¬a + 3 ≥ int.nat_abs ↑b) : 
    b % (a + 3) < nat.succ (nat.succ (nat.succ a)) := 
begin
    simp at h,
    suffices : (a+3) > 0, from nat.mod_lt b this,
    suffices : 0 ≠ (a+3), from (nat.pos_iff_ne_zero.mpr this.symm),
    trivial,
end

private def jacobi_sym_pos : ℕ → ℕ → ℤ
| a          0 := 0
| 0          (nat.succ b) := 0
| 1          (nat.succ b) := 1
| 2          (nat.succ b) := if (nat.succ b) % 8 = 1 ∨ (nat.succ b) % 8 = 7 then 1 else -1
| (nat.succ (nat.succ (nat.succ a))) (nat.succ b) := 
                if h1 : (a+3) ≥ int.nat_abs (nat.succ b) then 
                have (a + 3) % (nat.succ b) < nat.succ (nat.succ (nat.succ a)), from aux2 a b h1, 
                jacobi_sym_pos ((a+3)%(nat.succ b)) (nat.succ b) else
                (if h2 : (a+3) % 2 = 0 then 
                have 2 < nat.succ (nat.succ (nat.succ a)), from dec_trivial, 
                have (a + 3) / 2 < nat.succ (nat.succ (nat.succ a)), from nat.div_lt_self dec_trivial dec_trivial, 
                jacobi_sym_pos 2 (nat.succ b) * jacobi_sym_pos ((a+3)/2) (nat.succ b) else 
                have (nat.succ b) % (a + 3) < nat.succ (nat.succ (nat.succ a)), from aux3 a (nat.succ b) h1,
                (if (a+3) % 4 = 1 ∨ (nat.succ b) % 4 = 1  then jacobi_sym_pos ((nat.succ b) % (a+3)) (a+3) else -(jacobi_sym_pos ((nat.succ b) % (a+3)) (a+3))))
using_well_founded {rel_tac:= λ _ _, `[exact ⟨_, measure_wf (psigma.fst)⟩ ]}

private def jacobi_sym_aux : ℤ → ℤ → ℤ
| a     -[1+b] := 0
| (-1)       b := if b % 4 = 1 then 1 else -1 
| -[1+(nat.succ a)] b := 
                have 1 < nat.succ (nat.succ a), from dec_trivial, 
                jacobi_sym_pos (a+2) (int.nat_abs b) * jacobi_sym_aux (-1) b
| a          b := jacobi_sym_pos (int.nat_abs a) (int.nat_abs b)
using_well_founded {rel_tac:= λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ psigma.fst)⟩ ]}

/- Computes the Jacobi Symbol, extended to b even which will output 0, is it the Kronecker Symbol?-/
def jacobi_sym : ℤ → ℤ → ℤ
| a          1 := 1
| a          b := if b % 2 = 1 then jacobi_sym_aux a b else 0

-- an attempt at notation for the jacobi symbol
local notation {a|b} := jacobi_sym a b 

#eval {8|1}
-- #eval {-5|0}
-- #eval {-1|0}
-- #eval {-2|15}
-- #eval {-5|8}
-- #eval {1236|200011}

-- Properties of Jacobi symbol (taken from Wikipedia) --

theorem jacobi_sym_eq_legendre_sym (a n : ℤ) (hn : prime_int n ∧ (int.nat_abs n) ≠ 2) : {a|n} = legendre_sym a hn := sorry

theorem jacobi_sym_refl (a b n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) : a ≡ b [ZMOD n] →  {a|n} = {b|n} := sorry

theorem jacobi_sym_not_coprime (a n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) : int.gcd a n ≠ 1 → {a|n} = 0 := sorry

theorem jacobi_sym_num_mul (a b n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) : {a*b|n} = {a|n} * {b|n} := sorry

theorem jacobi_sym_denom_mul (a m n : ℤ) (m_pos_odd : m > 0 ∧ int.gcd 2 m = 1) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) : {a|m*n} = {a|m} * {a|n} := sorry

theorem jacobi_sym_quadratic_res (m n : ℤ) (m_pos_odd : m > 0 ∧ int.gcd 2 m = 1) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) [has_pow ℤ ℤ] : int.gcd m n = 1 → {m|n} * {n|m} = (-1)^(((m-1)/2)*((n-1)/2)) := sorry

theorem jacobi_num_zero (n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1): if n = 1 then {0|n} = 1 else {0|n} = 0 := sorry 

theorem jacobi_num_neg_one (n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) [has_pow ℤ ℤ] : {-1|n} = (-1)^((n-1)/2) := sorry

theorem jacobi_num_two (n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) [has_pow ℤ ℤ] :  {2|n} = (-1)^(((n^2)-1)/8) := sorry

--trying to state that jacobi_sym is equal to the product of legendre symbols, with prime factors p the prime factorisation of n
--lemma jacobi_eq_prod (a n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) : prod (factors pmap n) = jacobi_sym a n 

theorem jacobi_denom_one (a : ℤ) : jacobi_sym a 1 = 1 := by refl
