import analysis.real
 import data.nat.prime data.int.modeq data.complex.basic algebra.euclidean_domain number_theory.pell data.pnat
open nat
-- Questions:
 -- Find the continued fraction expansions of the following rational numbers:
-- 69/40
theorem q1a:
--theorem q1a:
 -- 233/144
theorem q1b:
--theorem q1b:
 -- 507/414
theorem q1c:
--theorem q1c:
 -- Define the Fibonacci numbers F(n) by F₁ = F₂ = 1, F(n+1) = F(n) + F(n-1) for i ≥ 2. Describe, for all n > 1, the continued fraction expansion of F(n)/F(n-1).
theorem q2a:
--theorem q2a:
 -- Find the continued fraction expansion of (1+sqrt(5))/2.
theorem q2b:
--theorem q2b:
 -- Show that the limit, as n goes to infinity, of F(n)/F(n-1) is (1+sqrt(5))/2.
theorem q2c:
--theorem q2c:
 -- Show that a positive integer n is expressible as x^2 - xy + y^2, with x and y integers, if and only if for every prime p congruent to 2 mod 3, the exponent of p in the prime factorization of n is even.
-- [Hint: Use unique factorization in the Eisenstein integers.]
theorem q3a:
theorem q3a (n p k : ℕ) (x y : ℤ) (hq: prime p) (hp: p ≡ 2 [MOD 3]): n = x^2 -x*y + y^2 ↔ ((p ∣ n ∧ p^k ∣ n) → k ≡ 0 [MOD 2]) := sorry
 -- Find x and y such that x^2 - xy + y^2 = 91.
theorem q3b:
--theorem q3b:
 -- Find all solutions to the equation x^2 - 10 y^2 = 1. Explicitly list all the solutions with x < 200 and x,y > 0.
theorem q4a:
--theorem q4a:
 -- Find all solutions to the equation x^2 - 10 y^2 = -1.
theorem q4b:
--theorem q4b:
 -- Find the value of the continued fraction [1;2,2,2,...].
theorem q5a:
--theorem q5a:
 -- Find the value of the continued fraction [1;3,5,1,3,5,...].
theorem q5b:
--theorem q5b:
 -- Show that, for n an integer, we have sqrt(n^2+1) = [n;2n,2n,2n,...].
theorem q6a:
--theorem q6a:
 -- Show that, for n an integer, we have sqrt(n^2+2) = [n;n,2n,n,2n,...].
theorem q6b: 
--theorem q6b: 