import data.nat.prime data.int.modeq data.complex.basic algebra.euclidean_domain number_theory.pell data.pnat

-- Questions:

structure gaussian_ints := 
(re : ℤ)
(im : ℤ)
-- this is the necessary structure for ℤ[i]
def gaussian_val (x : gaussian_ints) : ℕ := (x.re * x.re + x.im * x.im).nat_abs
-- and this is the valuation required.


-- 1.Give the prime factorisations, in ℤ[i], of the following elements of ℤ[i]. Be sure to justify that each of the factors is prime.
-- 221
--theorem q1a:

-- 7-9i
--theorem q1b: 

-- 12-i
--theorem q1c:

-- 2. Find a greatest common divisor, in ℤ[i], of the following elements of ℤ[i]:
-- 37 and 5+7i
--theorem q2a:

-- 52 and 9+7i
--theorem q2b:


-- 3. Let n be an integer. Show that if 4n is the sum of three squares, then so is n.
-- [Hint: If 4n = a^2+b^2+c^2, show that all of a, b and c must be even.]
-- would it make more sense to wlog a,b,c,d,e,f ∈ ℕ? 
theorem q3a (n a b c d e f : ℤ ) : (4*n = a^2 + b^2 + c^2) → (n = d^2 + e^2 + f^2) := sorry

-- Show that if n has the form 4^t(8k+7) for some nonnegative integer t and integer k, then n cannot be written as the sum of three squares.
-- (In fact, these are the only numbers that cannot be written as sum of three squares, but this is much harder.)
-- want t : pnat 
theorem q3b (n k a b c : ℤ) (t : ℕ) : (n = (4^t)*(8*k+7)) → n ≠ a^2 + b^2 + c^2 := sorry 

-- Use Fermat descent, starting with 557^2 + 55^2 = 26 . 12049 to write the prime 12049 as sum of two squares.
--theorem q4:

-- For each of the following n, either write n as the sum of two squares, or prove that it is not possible to do so:
-- 1865
-- ans: (29+32i)(29−32i) = 292 + 322.

--theorem q5a:

-- 77077
--ans: 77077 = (77·2)2 +(77·3)2.
--theorem q5b:

--609
-- ans: no.
theorem q5c (a b : ℕ) : 609 ≠ a^2 + b^2 := sorry

--7501
--ans: 7501 = (2+3i)(24+i)(2−3i)(24−i) = (45+74i)(45− 74i), so 7501 = 452 + 742.
--theorem q5d:

-- Let ζ = -1/2 + sqrt(-3)/2, and let ℤ[ζ] be the subset of ∁ consisting of all complex numbers of the form a+bζ, where a,b are integers.
-- Show that ℤ[ζ] is closed under addition and multiplication.
--theorem q6a:

-- Let N: ℤ[ζ] → ∁ be defined by N(z) = z­(bar z). Show that if z ∈ ℤ[ζ], then N(z) is an integer.
--theorem q6b:

-- Show that for any a,b ∈ ℤ[ζ], with b ≠ 0, there exist a q, r in ℤ[ζ] such that a = bq+r and N(r) < N(b).
--theorem q6c:

--Conclude that for any a,b in ℤ[ζ], a greatest common divisor of a and b exists.
--theorem q6d:

-- Show that an integer prime p remains prime in ℤ[ζ] if and only if p ≡ 2 (mod 3).
-- [Hint: First show that if p ≡ 1 (mod 3), then there exists n ∈ ℤ such that p divides n^2+n+1.]
--theorem q6e: