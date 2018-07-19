import tactic.norm_num chris_hughes_various.zmod data.nat.prime data.nat.basic data.int.modeq algebra.group_power group_theory.subgroup algebra.group data.set.basic group_theory.order_of_element
open nat 

universes u v w x
variables m p : ℕ 
variables {G : Type u} {H : Type v} 
variables [group G] [group H] [group (zmod 11)] [add_group (zmod m)] [group (zmod p)]

definition is_cyclic (G : Type*) [group G] := ∃ x : G, gpowers x = set.univ
-- *1. Suppose that G is a finite group which contains elements of each of the orders 1, 2, . . . , 10. What is the smallest possible value of |G|? Find a group of this size which does have elements of each of these orders.
--theorem sheet07_q1 (G : Type*) (g : group) : := sorry

-- 2. What is the largest order of an element of S₈?
    -- Ans: 15
-- theorem sheet07_q2:

-- 3. Let G be a cyclic group of order n, and g a generator. Show that gk is a generator for G if and only if hcf(k, n) = 1.
-- theorem sheet07_q3:

-- 4. Let G and H be finite groups. Let G×H be the set {(g,h)|g∈G,h∈H} with the binary operation (g1, h1) ∗ (g2, h2) = (g1g2, h1h2).
definition Cart_prod := prod G H 
--definition bin_op (G : Type*) (H : Type*) (g₁ g₂ : prod G H) := prod (g₁.1 * g₂.1) (g1.2 * g2.2)

-- (a) Show that (G×H,∗) is a group.
-- theorem sheet07_q4a:

-- (b) Show that if g ∈ G and h ∈ H have orders a, b respectively, then the order of (g,h) in G×H is the lowest common multiple of a and b.
-- theorem sheet07_q4b:

-- (c) Show that G × H is cyclic if and only if G and H are both cyclic, and hcf(|G|,|H|) = 1.
-- theorem sheet07_q4c:

-- 5. Say whether each of the following statements is true or false, giving a counterexample or a brief proof.
    -- all these are true lmao

-- (a) For any positive integer m, the group (ℤ_m,+) is cyclic.
--theorem sheet07_q5a (m : ℕ) : is_cyclic (zmod m) → true := sorry

-- (b) ℤ_11 is a cyclic group.
theorem sheet07_q5b : is_cyclic (zmod 11) → true := sorry

-- (c) If p is an odd prime, then ℤ_p has exactly one element of order 2.
--theorem sheet07_q5c (p : ℕ) (hp : prime p) (x : zmod p) : ∃! x ∈ zmod p := sorry

-- (d) If p is a prime number with p ≡ 4 mod 5,then the inverse of [5] in ℤ_p is 􏰀p+1􏰁.
theorem sheet07_q5d (p x : ℕ) (hp : prime p) (hq : p ≡ 4 [MOD 5]) : 5*x ≡ 1 [MOD p] → x = p+1 := sorry

theorem flittle_thm (n p : ℕ) (hp : prime p) : n ^ (p-1) ≡ 1 [MOD p] := sorry
-- 6. (a) Find the remainder when 5^110 is divided by 13.
    -- Ans: 12.

instance (n : ℕ) : pos_nat (succ n) := ⟨succ_pos _ ⟩ 

theorem sheet07_q6a: 5^110 ≡ 12 [MOD 13] := sorry
--begin 
--rw ← @zmod.cast_val_of_lt 5 13 dec_trivial,
--rw ← @zmod.cast_val_of_lt 12 13 dec_trivial,
--end

-- (b) Find the inverses of [2] and of [120] in ℤ_9871. (The number 9871 is prime.)
    -- Ans: 4936, 7321 respectively
theorem sheet07_q6bi (x : ℕ) : 2*x ≡ 1 [MOD 9871] → x = 4936 := sorry
theorem sheet07_q6bii (x : ℕ) : 120*x ≡ 1 [MOD 9871] → x = 7321 := sorry

-- (c) Use Fermat’s Little Theorem to show that n^17 ≡ n mod 255 for all n ∈ ℤ. 
theorem sheet07_q6c (n : ℕ) : n^17 ≡ n [MOD 255] := sorry

-- (d) Prove that if p and q are distinct prime numbers then p^(q-1) + q^(p−1) ≡ 1 mod pq.
theorem sheet07_q6d (p q : ℕ) (hp: prime p) (hq: prime q) : p^(q-1) + q^(p-1) ≡ 1 [MOD p*q] := sorry

-- 7. Let p be an odd prime.

-- (a) Prove that (p − 1)! ≡ −1 mod p (Wilson’s Theorem).
theorem sheet07_q7a (p : ℕ) (hp : prime p) : fact (p-1) ≡ -1 [ZMOD p] := sorry 

-- (b) Show that if p ≡ 1 mod 4,then there is x ∈ Z with x^2 ≡ −1 (mod p).
theorem sheet07_q7b (p : ℕ) (hp : prime p) (x : ℤ): p ≡ 1 [ZMOD 4] → x^2 ≡ -1 [ZMOD p] := sorry

-- (c) Show that if p ≠ 2 and there is x∈Z with x^2 ≡−1 modp,then p ≡ 1 mod 4.
theorem sheet07_q7c (p : ℕ) (hp : prime p) (x : ℤ) : p ≠ 2 ∧ x^2 ≡ -1 [ZMOD p] → p ≡ 1 [ZMOD 4] := sorry
