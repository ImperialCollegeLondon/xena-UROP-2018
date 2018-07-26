import chris_hughes_various.zmod data.fintype data.nat.prime data.nat.gcd data.nat.modeq algebra.ring

open nat 
open fintype

--adding phi function and lemmas

def phi (n : ℕ) := ((finset.range n).filter (nat.coprime n)).card
local notation `φ`  := phi 

instance {α : Type*} [fintype α] [monoid α] : fintype (units α) := sorry

lemma phi_n (n : ℕ) [pos_nat n] : phi n = card (units (zmod n)) := sorry

lemma phi_p (p : ℕ) (hp: prime p) : φ p = p-1 := sorry
-- begin
-- rw phi_n p,
-- sorry,
-- end

lemma strong_mult (m n : ℕ) : φ(m*n) = (φ m) * (φ n) * (gcd m n / φ (gcd m n)) := sorry

lemma phi_mult (n m : ℕ) (hp: gcd n m = 1) : φ (n*m) = (φ n) * (φ m) := sorry

lemma phi_odd_twice_eq_n (n : ℕ) (hp : gcd 2 n = 1) : φ (2*n) = φ n := 
begin 
rw phi_mult 2 n,
rw phi_p 2,
simp,
unfold prime,
split,
exact dec_trivial,
intros,
rwa ← dvd_prime (prime_two),
assumption,
end

lemma phi_even_twice_eq_twice_n (n : ℕ) (hp : gcd 2 n = 2) : φ (2*n) = 2 * φ n := 
begin 
rw strong_mult 2 n,
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

lemma power_p_phi (p k : ℕ) (hp: prime p) : φ p^k = (p^k)*(1-1/p) := sorry
--induction?
lemma dvd_phi (m n : ℕ) : (m ∣ n) → (φ m ∣ φ n) := 
begin
intros,
sorry,--assume (n = m * (n/m)),
end

lemma dvd_a_power (a n : ℕ) : n ∣ φ (a^n - 1) := sorry

lemma gcd_phi_eq_lcm_phi (m n d l : ℕ) (hp : d = gcd m n) (hq : l = lcm m n)  : φ l * φ d = φ m * φ n := sorry
-- begin
-- intros,
-- rw ← phi_mult l d,
-- rw [hp, hq],
-- rw [mul_comm, gcd_mul_lcm],
-- rw phi_mult,
-- end

--theorem phi_prod_p (n : ℕ) : φ n = 

--lemma exists_k (a : ℤ) (n k : ℕ) (hp : gcd a n = 1) : ∃ k, a^k ≡ 1 [MOD n] := sorry

--lemma ord_modeq (a : ℤ) (n k : ℕ) (hp : gcd a n = 1) (hq: a^k ≡ 1 [MOD n]) := sorry

--theorem euler_phi_thm (a n : ℕ) (hp: gcd a n = 1) : a^(phi n) ≡ 1 [MOD n] := sorry

--theorem flittlet (a p : ℕ) (hp : prime p) : a^(p-1) ≡ 1 [MOD p] := sorry
