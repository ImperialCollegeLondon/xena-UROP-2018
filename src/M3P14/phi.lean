import chris_hughes_various.zmod data.fintype data.nat.prime data.nat.gcd data.nat.modeq algebra.ring

open nat 
open fintype


--defining the phi function

definition phi (n : ℕ) := ((finset.range n).filter (nat.coprime n)).card
local notation `φ`  := phi 
instance {α : Type*} [fintype α] [monoid α] : fintype (units α) := sorry

--lemmas

theorem phi_n (n : ℕ) [pos_nat n] : phi n = card (units (zmod n)) := sorry

theorem phi_p (p : ℕ) (hp: prime p) : φ p = p-1 := sorry

theorem strong_mul (m n : ℕ) : φ(m*n) = (φ m) * (φ n) * (gcd m n / φ (gcd m n)) := sorry

theorem phi_mul (n m : ℕ) (hp: gcd n m = 1) : φ (n*m) = (φ n) * (φ m) := 
begin
    rw [nat.mul_comm, strong_mul],
    rw [nat.gcd_comm, hp],
    have h : φ 1 = 1, from dec_trivial,
    rw h,
    simp,
    rwa mul_comm,
end

theorem phi_odd_twice_eq_n (n : ℕ) (hp : gcd 2 n = 1) : φ (2*n) = φ n := 
begin 
rw phi_mul 2 n,
rw phi_p 2,
simp,
unfold prime,
split,
exact dec_trivial,
intros,
rwa ← dvd_prime (prime_two),
assumption,
end

theorem phi_even_twice_eq_twice_n (n : ℕ) (hp : gcd 2 n = 2) : φ (2*n) = 2 * φ n := 
begin 
rw strong_mul 2 n,
rw hp,
rw phi_p 2,
simp,
rw mul_comm,
unfold prime,
split,
exact dec_trivial,
intros,
rwa ← dvd_prime (prime_two),
end

theorem power_p_phi (p k : ℕ) (hp: prime p) : φ p^k = (p^k)*(1-1/p) := sorry

theorem dvd_phi (m n : ℕ) (hp : m > 0) : (m ∣ n) → (φ m ∣ φ n) := 
begin
intros,
have eq_n_m : n = m * (n / m), 
{
    rw ←nat.mul_div_assoc m a,
    rw mul_comm,
    rwa nat.mul_div_cancel,
},
have eq_2: φ m * φ (n / m) * (gcd m (n / m) / φ (gcd m (n / m))) = φ (m * (n / m)), from eq.symm (strong_mul m (n/m)),
have h5 : φ m ∣ φ m * (φ (n/m) * (gcd m (n/m) / φ (gcd m (n/m)))), from dvd_mul_right _ _,
have h6 : φ m * (φ (n/m) * (gcd m (n/m) / φ (gcd m (n/m)))) = φ m * φ (n / m) * (gcd m (n / m) / φ (gcd m (n / m))), by rw mul_assoc,
have h7 : φ m ∣ φ m * φ (n / m) * (gcd m (n / m) / φ (gcd m (n / m))), from eq.subst h6 h5,
have h8 : φ m ∣ φ (m * (n / m)), from eq.subst (strong_mul m (n/m)).symm h7,
exact eq.subst eq_n_m.symm h8,
end

theorem dvd_a_power (a n : ℕ) : n ∣ φ (a^n - 1) := sorry

theorem gcd_phi_eq_lcm_phi (m n d l : ℕ) (hp : d = gcd m n) (hq : l = lcm m n)  : φ l * φ d = φ m * φ n := sorry

theorem euler_phi_thm (a n : ℕ) (hp: gcd a n = 1) : a^(φ n) ≡ 1 [MOD n] := sorry

theorem flittlet (a p : ℕ) (hp : prime p) : a^(p-1) ≡ 1 [MOD p] := sorry

-- conjectures

theorem lehmers_conj (n : ℕ) (hp: ¬ (prime n)) : φ n ∣ n := sorry
