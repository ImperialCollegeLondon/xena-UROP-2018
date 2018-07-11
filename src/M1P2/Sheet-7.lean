import data.nat.prime data.nat.basic data.int.modeq
open nat 

-- (a) Prove that (p − 1)! ≡ −1 mod p (Wilson’s Theorem).
theorem sheet07_q7a (p : ℕ) (hp : prime p) : fact (p-1) ≡ -1 [ZMOD p] := sorry 
--- (b) Show that if p≡1 mod 4,then there is x∈Z with x^2 ≡−1 modp.
theorem sheet07_q7b (p : ℕ) (hp : prime p) : p ≡ 1 [ZMOD 4] → ∃ x ∈ ℤ ∧ x^2 ≡ -1 [ZMOD p] := sorry
-- (c) Show that if p ≠ 2 and there is x∈Z with x^2 ≡−1 modp,then p ≡ 1 mod 4.
theorem sheet07_q7c (p : ℕ) (hp : prime p) : p ≠ 2 ∧ ∃ x ∈ ℤ ∧ x^2 ≡ -1 [ZMOD p] → p ≡ 1 [ZMOD 4] := sorry
