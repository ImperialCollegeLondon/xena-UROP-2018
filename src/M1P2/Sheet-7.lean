import data.nat.prime data.nat.basic data.int.modeq
open nat 


--sheet 7

-- *1. Suppose that G is a finite group which contains elements of each of the orders 1, 2, . . . , 10. What is the smallest possible value of |G|? Find a group of this size which does have elements of each of these orders.
theorem sheet07_q1:

-- 2. What is the largest order of an element of S8?
theorem sheet07_q2:

-- 3. Let G be a cyclic group of order n, and g a generator. Show that gk is a
-- generator for G if and only if hcf(k, n) = 1.
theorem sheet07_q3:

-- 4. LetG and H be finite groups. Let G×H be the set {(g,h)|g∈G,h∈H} with the binary operation (g1, h1) ∗ (g2, h2) = (g1g2, h1h2).

-- (a) Show that (G×H,∗) is a group.
theorem sheet07_q4a:
-- (b) Show that if g ∈ G and h ∈ H have orders a, b respectively, then the order of (g,h) in G×H is the lowest common multiple of a and b.
theorem sheet07_q4b:
-- (c) Show that G × H is cyclic if and only if G and H are both cyclic, and hcf(|G|,|H|) = 1.
theorem sheet07_q4c:

-- 6. (a) Find the remainder when 5110 is divided by 13.
theorem sheet07_q6a:
-- (b) Find the inverses of [2] and of [120] in Z×9871. (The number 9871 is prime.)
theorem sheet07_q6b:
-- (c) Use Fermat’s Little Theorem to show that n17 ≡ n mod 255 for all n ∈ Z. (d) Prove that if p and q are distinct prime numbers then
-- pq−1 + qp−1 ≡ 1 mod pq.
theorem sheet07_q6c:

-- 7. Let p be an odd prime.
-- (a) Prove that (p − 1)! ≡ −1 mod p (Wilson’s Theorem).
theorem sheet07_q7a (p : ℕ) (hp : prime p) : fact (p-1) ≡ -1 [ZMOD p] := sorry 
--- (b) Show that if p≡1 mod 4,then there is x∈Z with x^2 ≡−1 modp.
theorem sheet07_q7b (p : ℕ) (hp : prime p) : p ≡ 1 [ZMOD 4] → ∃ x ∈ ℤ ∧ x^2 ≡ -1 [ZMOD p] := sorry
-- (c) Show that if p ≠ 2 and there is x∈Z with x^2 ≡−1 modp,then p ≡ 1 mod 4.
theorem sheet07_q7c (p : ℕ) (hp : prime p) : p ≠ 2 ∧ ∃ x ∈ ℤ ∧ x^2 ≡ -1 [ZMOD p] → p ≡ 1 [ZMOD 4] := sorry
