import data.nat.basic M3P14.order_zmodn_kmb data.int.basic M3P14.lqr

private theorem aux1 (a : ℕ): 
    1 < nat.succ (nat.succ a) := dec_trivial

private theorem aux2 (a b : ℕ) (h : a + 3 ≥ int.nat_abs ↑b) : 
    (a + 3) % (nat.succ b) < nat.succ (nat.succ (nat.succ a)) := 
begin
    simp at h,
    have neg : (nat.succ b) ≠ 0, trivial,
    suffices : (nat.succ b) < nat.succ (nat.succ (nat.succ a)), from lt_trans (nat.mod_lt (a + 3) (nat.pos_iff_ne_zero.mpr neg)) this,
    suffices : b + 1 < a + 3, by simp [this],
    suffices : b ≤ a + 3, sorry,
    exact h,
end

#print notation ≥
#
#check nat.lt_iff_le_not_le.mp
#check nat.lt_of_succ_le
#check nat.succ_le_of_lt
#check nat.lt_of_add_lt_add_left

private theorem aux3 (a b : ℕ) (h : ¬a + 3 ≥ int.nat_abs ↑b) : 
    2 < nat.succ (nat.succ (nat.succ a)) := dec_trivial

private theorem aux4 (a b : ℕ) : 
    (a + 3) / 2 < nat.succ (nat.succ (nat.succ a)) := 
begin
    suffices : (a+3)/2 < a+3, by simp [this], 
    exact nat.div_lt_self dec_trivial dec_trivial,
end

private theorem aux5 (a b : ℕ) (h : ¬a + 3 ≥ int.nat_abs ↑b) : 
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
                have 2 < nat.succ (nat.succ (nat.succ a)), from aux3 a (nat.succ b) h1, 
                have (a + 3) / 2 < nat.succ (nat.succ (nat.succ a)), from aux4 a (nat.succ b), 
                jacobi_sym_pos 2 (nat.succ b) * jacobi_sym_pos ((a+3)/2) (nat.succ b) else 
                have (nat.succ b) % (a + 3) < nat.succ (nat.succ (nat.succ a)), begin sorry end,
                (if (a+3) % 4 = 1 ∨ (nat.succ b) % 4 = 1  then jacobi_sym_pos ((nat.succ b) % (a+3)) (a+3) else -(jacobi_sym_pos ((nat.succ b) % (a+3)) (a+3))))
using_well_founded {rel_tac:= λ _ _, `[exact ⟨_, measure_wf (psigma.fst)⟩ ]}

private def jacobi_sym_aux : ℤ → ℤ → ℤ
| a     -[1+b] := 0
| (-1)       b := if b % 4 = 1 then 1 else -1 
| -[1+(nat.succ a)] b := 
                have 1 < nat.succ (nat.succ a), from aux1 a, 
                jacobi_sym_pos (a+2) (int.nat_abs b) * jacobi_sym_aux (-1) b
| a          b := jacobi_sym_pos (int.nat_abs a) (int.nat_abs b)
using_well_founded {rel_tac:= λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ psigma.fst)⟩ ]}

/- Computes the Jacobi Symbol, extended to b even which will output 0, is it the Kronecker Symbol?-/
def jacobi_sym : ℤ → ℤ → ℤ
| a          1 := 1
| a          b := if b % 2 = 1 then jacobi_sym_aux a b else 0


#eval jacobi_sym 8 1
#eval jacobi_sym (-5 : ℤ) 0
#eval jacobi_sym (-1 : ℤ) 0
#eval jacobi_sym (-2 : ℤ) 15
#eval jacobi_sym (-5 : ℤ) 8
#eval jacobi_sym 1236 200011

-- Properties of Jacobi symbol (taken from Wikipedia) --

theorem jacobi_sym_eq_legendre_sym (a n : ℤ) (hn : prime_int n ∧ (int.nat_abs n) ≠ 2) : jacobi_sym a n = legendre_sym a hn := sorry

theorem jacobi_sym_refl (a b n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) : a ≡ b [ZMOD n] → jacobi_sym a n = jacobi_sym b n := sorry

theorem jacobi_sym_not_coprime (a n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) : int.gcd a n ≠ 1 → jacobi_sym a n = 0 := sorry

theorem jacobi_sym_num_mul (a b n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) : jacobi_sym (a*b) n = jacobi_sym a n * jacobi_sym b n := sorry

theorem jacobi_sym_denom_mul (a m n : ℤ) (m_pos_odd : m > 0 ∧ int.gcd 2 m = 1) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) : jacobi_sym a m*n = jacobi_sym a m * jacobi_sym a n := sorry

theorem jacobi_sym_quadratic_res (m n : ℤ) (m_pos_odd : m > 0 ∧ int.gcd 2 m = 1) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) [has_pow ℤ ℤ] : int.gcd m n = 1 → jacobi_sym m n * jacobi_sym n m = (-1)^(((m-1)/2)*((n-1)/2)) := sorry

theorem jacobi_num_zero (n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1): if n = 1 then jacobi_sym 0 n = 1 else jacobi_sym 0 n = 0 := sorry 

theorem jacobi_num_neg_one (n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) [has_pow ℤ ℤ] : jacobi_sym (-1) n = (-1)^((n-1)/2) := sorry

theorem jacobi_num_two (n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) [has_pow ℤ ℤ] : jacobi_sym 2 n = (-1)^(((n^2)-1)/8) := sorry

theorem jacobi_denom_one (a : ℤ) : jacobi_sym a 1 = 1 := sorry
