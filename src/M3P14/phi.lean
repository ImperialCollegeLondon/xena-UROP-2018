import data.nat.modeq data.nat.gcd number_theory.pell data.int.modeq data.finset chris_hughes_various.zmod data.fintype

open nat 
open fintype

--adding phi function and lemmas

def phi (n : nat) := ((finset.range n).filter (nat.coprime n)).card
--local notation Φ(n) := phi n 
lemma phi_p (p : ℕ) (hp: prime p) : phi p = p-1 := sorry
--lemma phi_n (n : ℕ) : phi n = card (units (zmod n)) := sorry
--lemma phi_mult (n m : ℕ) (hp: gcd n m = 1) : phi n*m = (phi n) * (phi m) := sorry
--lemma exists_k (a : ℤ) (n k : ℕ) (hp : gcd a n = 1) : ∃ k, a^k ≡ 1 [MOD n] := sorry
--lemma ord_modeq (a : ℤ) (n k : ℕ) (hp : gcd a n = 1) (hq: a^k ≡ 1 [MOD n]) := sorry
--theorem euler_phi_thm (a n : ℕ) (hp: gcd a n = 1) : a^(phi n) ≡ 1 [MOD n] := sorry
--theorem flittlet (a p : ℕ) (hp : prime p) : a^(p-1) ≡ 1 [MOD p] := sorry

#check phi 5