import data.nat.prime data.nat.gcd data.nat.modeq data.nat.gcd M3P14.phi

open nat

def order (a n k : ℕ) := ∀m : ℕ, coprime a n ∧ (a^k) ≡ 1 [MOD n]
                                          ∧ (a^m) ≡ 1 [MOD n] → k ≤ m

theorem order_div (a n k d : ℕ) (h : order a n k) : (a^d) ≡ 1 [MOD n] → k ∣ d := sorry

lemma order_div_phi_n (a n k: ℕ) (h1 : coprime a n) (h2 : order a n k) : k ∣ phi n := sorry

def primitive_root (a n : ℕ) := ∃ k : ℕ, coprime a n ∧ order a n k → k = phi n 

theorem primitive_root_existence (n : ℕ) : ∃ a : ℕ, (primitive_root a n) ↔ n = 1 ∨ n = 2 ∨ n = 4 ∨ ∃ p r : ℕ, prime p ∧ r > 0 → (n = p^r ∨ n = 2*p^r) := sorry

lemma exists_pow_eq_one_mod_n (a n : ℕ) : ∃i≠0, a ^ i ≡ 1 [MOD n] := sorry

def order_of (a n : ℕ) : ℕ := nat.find (exists_pow_eq_one_mod_n a n)

def prim_root (a n : ℕ) := order_of a n = phi n

lemma order_of_div (a n k d : ℕ) (h1: order_of a n = k) (h2: a^d ≡ 1 [MOD n]) : k ∣ d := sorry

lemma order_of_div_phi_n (a n : ℕ) : order_of a n ∣ phi n := sorry 

lemma pow_order_of_eq_one (a n : ℕ) : a ^ (order_of a n) ≡ 1 [MOD n] := sorry 