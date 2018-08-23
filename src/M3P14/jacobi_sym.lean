import data.nat.basic M3P14.order_zmodn_kmb data.int.basic M3P14.lqr data.nat.prime 

private theorem aux1 (a b : ℕ) (h : ¬a + 3 = b + 1) : 
    b + 1 ≠ a + 3 := by {intro h2, exact absurd h2.symm h}

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
    suffices : b + 1 ≤ a + 3, from lt_of_le_of_ne this (aux1 a b h_1),
    exact h2,
end

private theorem aux3 (a b : ℕ) (h : ¬a + 3 ≥ int.nat_abs ↑b) : 
    b % (a + 3) < nat.succ (nat.succ (nat.succ a)) := 
begin
    suffices : (a+3) > 0, from nat.mod_lt b this,
    from dec_trivial,
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
def jacobi_algorithm : ℤ → ℤ → ℤ
| a          1 := 1
| a          b := if b % 2 = 1 then jacobi_sym_aux a b else 0

-- an attempt at notation for the jacobi symbol
local notation {a|b} := jacobi_algorithm a b 

#eval {8|1}
#eval {-5|0}
#eval {1236|200011}

-- Thank you Chris
lemma dvd_prod {α : Type*} [comm_semiring α] {a} {l : list α} (ha : a ∈ l) : a ∣ l.prod :=
let ⟨s, t, h⟩ := list.mem_split ha in
by rw [h, list.prod_append, list.prod_cons, mul_left_comm]; exact dvd_mul_right _ _

-- New definition of Jacobi symbol for positive and odd b to prove theorems
noncomputable definition jacobi_symbol {n : ℤ} (a : ℤ) (hn : n > 0 ∧ int.gcd 2 n = 1) := 
list.prod ((nat.factors n.nat_abs).pmap (λ (p : ℕ) hp, @legendre_sym p a hp)
begin
intros,
have h1: prime_int ↑a_1 = nat.prime a_1, refl,
have h2: int.nat_abs ↑a_1 = a_1, refl,
rw [h1, h2],
have h3: nat.prime a_1, from nat.mem_factors H,
have h4: a_1 ≠ 2,
{
    have j1: list.prod (nat.factors (int.nat_abs n)) = int.nat_abs n, from nat.prod_factors (int.nat_abs_pos_of_ne_zero (ne.symm (ne_of_lt hn.1))),
    assume j2,
    have j3: 2 = int.nat_abs 2, refl,
    have j4: a_1 ∣ list.prod (nat.factors (int.nat_abs n)), from dvd_prod H,
    rw [j1,j2,j3] at j4,
    unfold int.gcd at hn,
    have j5: nat.gcd (int.nat_abs 2) (int.nat_abs n) = int.nat_abs 2 ,from nat.gcd_eq_left j4,
    have j6: int.nat_abs 2 ≠ 1, from dec_trivial,
    exact absurd (hn.2) (eq.subst j5.symm j6),
},
exact ⟨h3,h4⟩,
end)

-- Properties of Jacobi symbol (taken from Wikipedia) --
set_option trace.check true
theorem jacobi_sym_eq_legendre_sym (a n : ℤ) (hn : prime_int n ∧ (int.nat_abs n) ≠ 2) : {a|n} = legendre_sym a hn := 
begin
    unfold legendre_sym,
    cases (classical.em (n = 1)),
    rw h at hn,
    have : ¬prime_int 1, unfold prime_int,
    suffices : ¬nat.prime 1, by simp [this],
    exact dec_trivial,
    exact absurd hn.1 this,
    have h2 : n ≠ 1, by simp [h],
    rw [jacobi_algorithm.equations._eqn_2 a n h],
    cases (classical.em (n % 2 = 1)),
    simp [h_1],
    split_ifs,
    sorry,
    sorry,
    sorry,
    split_ifs,
    exfalso,
    have := odd_prime_int_is_odd hn,
    exact absurd this h_1,
    refl,
    exfalso,
    have := odd_prime_int_is_odd hn,
    exact absurd this h_1,
end

lemma mod_eq_of_quad (a b n : ℤ) (hp: a ≡ b [ZMOD n]) : quadratic_res a n → quadratic_res b n := 
begin
unfold quadratic_res,
simp,
intros,
have h1 := int.nat_abs_dvd.2 (int.modeq.modeq_iff_dvd.1 hp.symm),
have h := int.modeq.trans (int.modeq.modeq_iff_dvd.2 h1) a_1,
existsi x,
exact h,
end

theorem jacobi_sym_refl (a b n : ℤ) (hn : n > 0 ∧ int.gcd 2 n = 1) : a ≡ b [ZMOD n] → jacobi_symbol a hn = jacobi_symbol b hn := 
begin
intros,
unfold jacobi_symbol,
simp,
sorry,
end

theorem jacobi_sym_not_coprime (a n : ℤ) (hn : n > 0 ∧ int.gcd 2 n = 1) : int.gcd a n ≠ 1 → jacobi_symbol a hn = 0 := 
begin 
intros,
dunfold jacobi_symbol,
simp,
sorry,
end

theorem jacobi_sym_num_mul (a b n : ℤ) (hn : n > 0 ∧ int.gcd 2 n = 1) : jacobi_symbol (a*b) hn = jacobi_symbol a hn * jacobi_symbol b hn := sorry

theorem jacobi_sym_denom_mul (a m n : ℤ) (m_pos_odd : m > 0 ∧ int.gcd 2 m = 1) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) : {a|m*n} = {a|m} * {a|n} := sorry

theorem jacobi_sym_quadratic_res (m n : ℤ) (m_pos_odd : m > 0 ∧ int.gcd 2 m = 1) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) [has_pow ℤ ℤ] : int.gcd m n = 1 → {m|n} * {n|m} = (-1)^(((m-1)/2)*((n-1)/2)) := sorry

theorem jacobi_num_zero (n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1): if n = 1 then {0|n} = 1 else {0|n} = 0 := sorry 

theorem jacobi_num_neg_one (n : ℤ) (hn : n > 0 ∧ int.gcd 2 n = 1) [has_pow ℤ ℤ] : {-1|n} = (-1)^((n-1)/2) := sorry

theorem jacobi_num_two (n : ℤ) (n_pos_odd : n > 0 ∧ int.gcd 2 n = 1) [has_pow ℤ ℤ] :  {2|n} = (-1)^(((n^2)-1)/8) := sorry

-- do we really need this, considering as it's true by def?
theorem jacobi_denom_one (a : ℤ) : {a|1} = 1 := by refl
