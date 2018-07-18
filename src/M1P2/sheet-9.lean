import algebra.ring algebra.group_power data.nat.prime data.nat.prime data.nat.basic data.int.modeq algebra.group_power group_theory.subgroup algebra.group data.set.basic data.nat.gcd init.algebra.ring data.nat.sqrt
open nat
-- 1. Let d ∈ Z be such that ℤ ∌ √d ,and let x,y ∈ Z[√d]. Verify the identity N(xy) = N(x)N(y), where N(r+s√d)=r^2−ds^2.
--theorem sheet9_q1 (d : ℤ) : (d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4]) → N(x)*N(y) = N(x*y) := sorry

-- 2. Let R bearing with unity, and let u be a unit in R. Show that u√n us a unit  for any n ∈ Z. Hence or otherwise, show that the the ring Z[√2] has infinitely many units.
-- 3∗. Suppose R is a finite integral domain. Prove that R is a field. Look carefully at your proof. To what extent does your proof make full use of the hypotheses? Formulate and prove a more general result about finite commutative rings with unity.
-- 4. Which of the following elements are irreducible in the rings specified?
-- (a) 2 ∈ Z[i]. 
-- (b) 1+2√2 ∈ Z[√2]. 
-- (c) 1+2√−2 ∈ Z[√−2]. 
-- (d) 5 ∈ Z[i].
-- (e) 7 ∈ Z[i].
-- (f) x^2+3x+1 ∈ Q[x].
-- (g) x^2−x−6 ∈ Q[x]. 
-- (h) x^4+x^2+1 in Q[x].
-- (i) x^3+3x+2 ∈ Z7[x].
-- 5. Factorize the following ring elements into irreducibles.
-- (a) 3 + 5i ∈  Z[i]. 
    --e.g 1+i,4+i
-- (b) 4+2√−2 ∈  Z[√−2]
    -- 
-- (c) x^6−1 ∈  R[x].
-- 6. Use the Euclidean algorithm to find the highest common factor for each of
-- the following pairs.
-- (a) 3+√3 and 12 ∈ Z[√3]. 
-- (b) 7+i and 5+3i ∈ Z[i].
-- (c) x^6 and x^8+x^7+1 ∈ C[x]. 
-- (d) x^3+x+1 and x5+1 ∈ R[x].