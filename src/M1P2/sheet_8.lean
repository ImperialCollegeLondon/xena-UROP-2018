import algebra.ring algebra.group_power data.nat.prime data.nat.prime data.nat.basic data.int.modeq algebra.group_power group_theory.subgroup algebra.group data.set.basic
open nat

-- 1. (a) Suppose n > 1 is a power of a prime number. Give a formula for the number of elements in the group (Z×n ; ·), explaining your answer.
-- euler totient function
--ef euler_tot (n : ℕ)
--theorem (ha: prime p) (n α : nat) (hp : n = p^α) :

-- (b) Find natural numbers n,m such that the residue class [m]n ∈ Z×n has order 5.
-- theorem sheet8_q1_b (m n : ℕ) 

-- *2. Show that the following sets are rings with the given binary operations. In each case, describe the units.
-- (a) The set {a/b ∈ Q| b odd} ,with the usual + and ·  b
--def s₁ : {a/b ∈ ℚ ∣ b = 2k+1}
-- (b) The set of all functions f : [0,1] −→ C, with + and · given by (f₁  + f₂)(x) = f₁(x) + f₂(x), (f₁ · f₂)(x) = f₁(x)f₂(x).
--def s₂ :
-- (c) The set P(N) of all subsets of N, with the operations X+Y=X∪Y\X∩Y (the symmetric difference of X and Y), X·Y =X∩Y.

-- 3. Suppose R is a ring and S ⊆ R. Devise a criterion which enables you to check whether S with the operations inherited from R is a ring (i.e. invent a test for being a subring). If R is a ring with unity, does your criterion imply that S is a ring with unity? √√√

-- 4. Let d ∈ Z and Q[√d] = {x+y d|x,y∈Q}. Prove that Q[√d]is a ring with the usual operations + and · in C. 
-- Show that every non-zero element of Q[√d]is a unit (so Q[√d] is a field).

-- 5. (a) Suppose that f(x) ∈ C[x] is non-zero and has n distinct roots. Prove that deg f ≥ n.
-- (b) Let f(x) ∈ R[x] be a polynomial with real coefficients. Show that if a ∈ C is a root of f(x), then its complex conjugate a is also a root of f(x). Deduce that if f(x) is an irreducible polynomial in R[x] then deg f ≤ 2.

-- 6. (a) Let f(x) ∈ Q[x] be a polynomial of degree at most 3 which has no rational root. Prove that f(x) is irreducible.
-- (b) Show that the polynomial f(x) = x^3 + x^2 + x + 3 is irreducible in Q[x].