--import data.nat.gcd
--import algebra.euclidean_domain

namespace nat

-- TODO: import mathlib, use their polymorphic definition of gcd
-- TODO: change some theorem signatures from ℕ to ℤ 

-- Show that for a, b, d integers, we have (da, db) = d(a,b)
theorem q1a (a b d : ℕ) : gcd (d*a) (d*b) = d * (gcd a b) := gcd_mul_left d a b

-- Let a, b, n integers, and suppose that n|ab. Show that n/(a,b) divides b
theorem q1b (a b n : ℕ) (ha : a > 0) (hn : n > 0) : n ∣ (a*b) → (n / gcd a n) ∣ b := λ h,
have n / gcd n a ∣ b * (a / gcd n a) := dvd_of_mul_dvd_mul_right (gcd_pos_of_pos_left a hn) 
begin
  rw ← nat.mul_div_assoc _ (gcd_dvd_right n a),
  rw nat.div_mul_cancel (gcd_dvd_left n a),
  rw mul_comm b,
  rwa nat.div_mul_cancel (dvd_trans (gcd_dvd_left n a) h),
end,
begin
  cases exists_eq_mul_left_of_dvd h with c hc,
  have := coprime.dvd_of_dvd_mul_right 
    (coprime_div_gcd_div_gcd (gcd_pos_of_pos_left a hn)) this,
  rwa gcd_comm,
end

-- Express 18 as an integer linear combination of 327 and 120.
theorem q2a : ∃ x y : ℕ, 18 = 327*x + 120*y := sorry

-- Find, with proof, all solutions to the linear diophantine equation 100x + 68y = 14
-- theorem q2b : ∀ x y : ℕ, 100*x + 68*y = 14 := sorry

-- Find a multiplicative inverse of 31 modulo 132
-- theorem q2c

-- Find an integer congruent to 3 mod 9 and congruent to 1 mod 49
theorem q2d : ∃ x : ℕ, x % 9 = 3 → x % 49 = 1 := sorry

-- Find, with proof, the smallest nonnegative integer n such that n = 1 (mod 3), n = 4 (mod 5), and n = 3 (mod 7)
theorem q2e : ∃ n : ℕ, ∀ n₂ : ℕ, n % 3 = 1 → n % 5 = 4 → n % 7 = 3
                            → n₂ % 3 = 1 → n₂ % 5 = 4 → n₂ % 7 = 3 → n ≤ n₂ 
                            := sorry

-- Let m and n be integers. Show that the greatest common divisor of m and n is the unique positive integer d such that:
--      - d divides both m and n, and
--      - if x divides both m and n, then x divides d.
theorem q3 : ∀ m n : ℕ, ∃! d : ℕ, ∀ x : ℕ, gcd m n = d → d ∣ m → d ∣ n → x ∣ m → x ∣ n → x ∣ d
                                    := sorry

-- Let a and b be nonzero integers. Show that there is a unique positive integer m with the following two properties:
--      - a and b divide m, and
--      - if n is any number divisible by both a and b, then m|n
-- The number m is called the least common multiple of a and b
theorem q4a : ∀ a b : ℕ, ∃! m : ℕ, ∀ n : ℕ, ¬(a = 0) → ¬(b = 0) →   
                                a ∣ m → b ∣ m → a ∣ n → b ∣ n → m ∣ n
                                := sorry 

-- Show that the least common multiple of a and b is given by |ab|/(a,b)
-- theorem q4b

-- Let m and n be 


end nat
