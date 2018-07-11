import data.nat.gcd
import data.nat.modeq
import data.nat.prime
import tactic.norm_num
import data.nat.gcd
open classical 

namespace nat

-- TODO : change ℕ to ℤ, but before that need to extend gcd to integers.

-- Show that for a, b, d integers, we have (da, db) = d(a,b).
theorem q1a (a b d : ℕ) : gcd (d*a) (d*b) = d * (gcd a b) := gcd_mul_left d a b

-- Let a, b, n integers, and suppose that n|ab. Show that n/(a,b) divides b.
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
theorem q2a : ∃ x y : ℤ, 18 = 327*x + 120*y := 
    ⟨-66, 180, by norm_num⟩

-- Find, with proof, all solutions to the linear diophantine equation 100x + 68y = 14.
theorem q2b : ∀ x y : ℤ, 100*x + 68*y = 14 := sorry

-- Find a multiplicative inverse of 31 modulo 132.
--theorem q2c :
theorem q2c : ∃ x : ℤ, 31*x % 132 = 1 := 
    ⟨115, by norm_num⟩

-- Find an integer congruent to 3 mod 9 and congruent to 1 mod 49.
theorem q2d : ∃ x : ℤ, x % 9 = 3 → x % 49 = 1 :=  
    ⟨-195, by norm_num⟩

theorem extended_chinese_remainder 
{p q r : ℕ}
(co : coprime p q ∧ coprime q r ∧ coprime r p) (a b c: ℕ) : {k // k ≡ a [MOD p] ∧ k ≡ b [MOD q] ∧ k ≡ c[MOD r]} :=sorry 


-- Find, with proof, the smallest nonnegative integer n such that n = 1 (mod 3), n = 4 (mod 5), and n = 3 (mod 7).
theorem q2e : ∃ n : ℕ, ∀ n₂ : ℕ, n % 3 = 1 ∧ n % 5 = 4 ∧ n % 7 = 3
                            → n₂ % 3 = 1 ∧ n₂ % 5 = 4 ∧ n₂ % 7 = 3 → n ≤ n₂ 
                            := 
begin
--@extended_chinese_remainder 3 5 7 dec_trivial 1 4 3
let n := 94,
let p := λ n, n % 3 = 1 ∧ n % 5 = 4 ∧ n % 7 = 3,
have h : ∃ n : ℕ, p n, from  ⟨94, dec_trivial⟩,
apply exists.intro (nat.find h),
assume n₂ hn hn₂,
exact nat.find_min' h hn₂,
end 




-- Let m and n be integers. Show that the greatest common divisor of m and n is the unique positive integer d such that:
--      - d divides both m and n, and
--      - if x divides both m and n, then x divides d.
theorem q3 : ∀ m n : ℕ, ∃! d : ℕ, ∀ x : ℤ, gcd m n = d → d ∣ m → d ∣ n → x ∣ m → x ∣ n → x ∣ d
                                    := sorry

-- Let a and b be nonzero integers. Show that there is a unique positive integer m with the following two properties:
--      - a and b divide m, and
--      - if n is any number divisible by both a and b, then m|n.
-- The number m is called the least common multiple of a and b.  
 
 
theorem gcd_dvd_trans {a b c : ℕ} : a ∣ b → b ∣ c → a ∣ c := 
begin 
  intro Hab, 
  intro Hbc, 
  cases Hab with e He, 
  cases Hbc with f Hf, 
  existsi e * f, 
  rw Hf, 
  rw He, 
  exact mul_assoc _ _ _, 
end  

variables a b c : ℕ 
variables (h1 : (a ∣ b)) (h2 : (b ∣ c))

theorem q4a : ∀ a b : ℕ, ∃! m : ℕ, ∀ n : ℕ, a ≠ 0 ∧ b ≠ 0 ∧   
                                a ∣ m ∧ b ∣ m ∧ a ∣ n ∧ b ∣ n → m ∣ n
                                := 
begin 
--existence
--define m = ab/(a,b) , a=da', b=db' → d ∣ n, a'∣ n, b'∣ n → m= da'b' ∣n as d, a', b' is coprime 
intro a, intro b,
let m := a*b/(gcd a b),
apply exists_unique.intro m,
{
  assume n,
  assume h,
  let a' := a/(gcd a b), 
  let b':= b/(gcd a b),
  let d:= gcd a b,
  cases em (coprime d a' ∨ coprime d b') with h1 h2,
  {
    cases h1 with cda' cdb',
    {
      have a'_dvd_a : a' ∣ a, sorry,
      have a_dvd_n : a ∣ n, sorry,
      have a'_dvd_n : a' ∣ n, from gcd_dvd_trans a'_dvd_a a_dvd_n,  
      have cba' : coprime b a', sorry, --coprime.coprime_mul_left_right a (d * b'),
      sorry,
    },
    {
      sorry, 
    }
  },
  {
    sorry,
  }
},
{
  sorry,
}
end 

#print coprime

-- Show that the least common multiple of a and b is given by |ab|/(a,b)
-- TODO: need to change ℕ to ℤ and use abs(a*b)
theorem q4b : ∀ a b : ℕ, lcm a b = a*b/(gcd a b) := 
begin
  intros a b,
  exact gcd_mul_lcm a b,
  sorry
end


-- Let m and n be positive integers, and let K be the kernel of the map:
--      ℤ/mnℤ → ℤ/mℤ x ℤ/nℤ 
-- that takes a class mod mn to the corresponding classes modulo m and n.
-- Show that K has (m, n) elements. What are they?
-- theorem q5 :

-- -- Show that the equation ax = b (mod n) has no solutions if b is not divisible by (a, n), and exactly (a, n) solutions in ℤ/n otherwise.
-- theorem q6 :
-- Show that the equation ax = b (mod n) has no solutions if b is not divisible by (a, n), and exactly (a, n) solutions in ℤ/n otherwise.
-- TODO: how to specify "there are exactly n solutions to an equation"?
--theorem q6 :  ¬(gcd a n ∣ b) → ¬(∃ x, a*x ≡ b [MOD n])

-- -- For n a positive integer, let σ(n) denote the sum Σ d for d∣n and d>0, of the positive divisors of n.
-- -- Show that the function n ↦ σ(n) is multiplicative.
-- theorem q7 :
--finset.range

-- Let p be a prime, and a be any integer. Show that a^(p²+p+1) is congruent to a^3 modulo p.
lemma nat.pow_mul (a b c : ℕ) : a ^ (b * c) = (a ^ b) ^ c :=
begin
  induction c with c ih,
  simp,
  rw [nat.mul_succ, nat.pow_add, nat.pow_succ, ih],
end

lemma nat.pow.mul (a b p q: ℕ) : a ≡ b [MOD q] → a ^ p ≡ b ^ p [MOD q] :=
begin 
  intro h,
  induction p with p ih,
  simp,
  rw [nat.pow_succ, nat.pow_succ], 
  apply nat.modeq.modeq_mul ih h,
end 

theorem fermat_little_theorem : ∀ a p : ℕ, prime p → a ^ p ≡ a [MOD p] := sorry

theorem q8 : ∀ a p : ℕ, prime p →  a^(p^2+p+1) ≡ a^3 [MOD p] := 
begin 
  assume a p hp,
  rw [nat.pow_add, nat.pow_one, nat.pow_add, nat.pow_succ, nat.pow_one, nat.pow_succ, nat.pow_succ, nat.pow_one],
  apply nat.modeq.modeq_mul,
  apply nat.modeq.modeq_mul,
  rw nat.pow_mul,
  have middle_step : (a ^ p) ^ p ≡ a ^ p [MOD p],
  let b := a ^ p,
  exact fermat_little_theorem b p hp,

  exact modeq.trans middle_step (fermat_little_theorem a p hp),
  exact fermat_little_theorem a p hp,
  exact modeq.refl a,
end 

-- Let n be a squarefree positive integer, and suppose that for all primes p dividing n, we have (p-1)∣(n - 1).
-- Show that for all integers a with (a, n) = 1, we have a^n = a (mod n).

def square_free_int (a : ℕ) := ∀ n : ℕ, (n*n) ∣ a → n = 1

theorem q9 : ∀ n p a, square_free_int n ∧ prime p ∧ p ∣ n → (p-1)∣(n - 1) → gcd a n = 1 → a^n ≡ a [MOD n] := sorry

-- Let n be a positive integer. Show that Σ Φ(d) for d∣n and d>0 = n.
-- [Hint: First show that the number of integers a with a ≤ 0 < n and (a, n) = n/d is equal to Φ(d).] 
--theorem q10 :

end nat
