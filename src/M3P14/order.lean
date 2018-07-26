import data.nat.prime data.nat.gcd data.nat.modeq data.nat.gcd M3P14.phi

open nat

def order (a n k : ℕ) := ∀m : ℕ, coprime a n ∧ (a^k) ≡ 1 [MOD n]
                                          ∧ (a^m) ≡ 1 [MOD n] → k ≤ m

def primitive_root (a n : ℕ) := ∃ k : ℕ, coprime a n ∧ order a n k → k = phi n 

theorem primitive_root_prime {p : ℕ} (h : prime p) : ∃ a : ℕ, (primitive_root a p) := sorry
