import data.nat.prime data.nat.gcd data.nat.modeq data.nat.gcd M3P14.phi

open nat

def order (a n k : ℕ) := ∀m : ℕ, coprime a n ∧ (a^k) ≡ 1 [MOD n]
                                          ∧ (a^m) ≡ 1 [MOD n] → k ≤ m

theorem order_div (a n k d : ℕ) (h : order a n k) : (a^d) ≡ 1 [MOD n] → k ∣ d := sorry

lemma order_div_phi_n (a n k: ℕ) (h1 : coprime a n) (h2 : order a n k) : k ∣ phi n := sorry

def primitive_root (a n : ℕ) := ∃ k : ℕ, coprime a n ∧ order a n k → k = phi n 

theorem primitive_root_existence (n : ℕ) : ∃ a : ℕ, (primitive_root a n) ↔ n = 1 ∨ n = 2 ∨ n = 4 ∨ ∃ p r : ℕ, prime p ∧ r > 0 → (n = p^r ∨ n = 2*p^r) := sorry