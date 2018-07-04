import data.nat.gcd
namespace nat

def divides : ℕ → ℕ → bool
| x y := x ≤ y ∧ gcd x y > 1

-- Show that for a, b, d integers, we have (da, db) = d(a,b)
theorem q1a (a b d : ℕ) : gcd (d*a) (d*b) = d * (gcd a b) := sorry

-- Let a, b, n integers, and suppose that n|ab. Show that n/(a,b) divides b 
theorem q1b (a b n : ℕ) : divides n (a*b) → divides (n / gcd a b) b := sorry

-- Express 18 as an integer linear combination of 327 and 120.
theorem q2a : ∃ x y : ℕ, 18 = 327*x + 120*y := sorry

-- Find, with proof, all solutions to the linear diophantine equation 100x + 68y = 14
-- theorem q2b : ∀ x y : ℕ, 100*x + 68*y = 14 := sorry

-- Find a multiplicative inverse of 31 modulo 132
-- theorem q2c

-- Find an integer congruent to 3 mod 9 and congruent to 1 mod 49
theorem q2d : ∃ x : ℕ, x % 9 = 3 ∧ x % 49 = 1 := sorry

-- Find, with proof, the smallest nonnegative integer n such that n = 1 (mod 3), n = 4 (mod 5), and n = 3 (mod 7)
theorem q2e : ∃ n : ℕ, ∀ n₂ : ℕ, (n % 3 = 1 ∧ n % 5 = 4 ∧ n % 7 = 3
                            ∧ n₂ % 3 = 1 ∧ n₂ % 5 = 4 ∧ n₂ % 7 = 3) → (n ≤ n₂) := sorry

-- Let m and n be integers. Show that the greatest common divisor of m and n is the unique positive integer d such that:
--     - d divides both m and n, and
--     - if x divides both m and n, then x divides d.
-- theorem q3 : ∀ x y : ℕ, gcd m n = 

