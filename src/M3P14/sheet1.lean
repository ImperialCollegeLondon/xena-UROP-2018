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

-- TODO: to find in mathlib
theorem coprime_dvd_of_dvd_mul {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : coprime a b) : a*b ∣ c := sorry 

theorem q4a : ∀ a b : ℕ, ∃! m : ℕ, ∀ n : ℕ, a ≠ 0 ∧ b ≠ 0 ∧   
                                a ∣ m ∧ b ∣ m ∧ a ∣ n ∧ b ∣ n → m ∣ n
                                := 
begin 
--existence
--define m = ab/(a,b) , a=da', b=db' → d ∣ n, a'∣ n, b'∣ n → m= da'b' ∣n as d, a', b' is coprime 
intro a, intro b,
let m := a*b/(gcd a b),
have m_def : m = a*b/(gcd a b), by simp,
apply exists_unique.intro m,
{
  assume n,
  assume h,
  have a_dvd_n : a ∣ n, from h.right.right.right.right.left,
  have b_dvd_n : b ∣ n, from h.right.right.right.right.right,
  let a' := a/(gcd a b), 
  have ap_eq : a/(gcd a b) = a', by simp,
  have gcd_dvd_a : (gcd a b) ∣ a, from gcd_dvd_left _ _,
  have gcd_dvd_b : (gcd a b) ∣ b, from gcd_dvd_right _ _,
  let b':= b/(gcd a b),
  have bp_eq : b' = b/(gcd a b), by simp,
  let d := gcd a b,
  have d_eq : d = gcd a b, by simp,

  cases em (coprime d a' ∨ coprime d b') with h1 h2,
  {
      have eq_a_bis : a = gcd a b * a', from nat.eq_mul_of_div_eq_right gcd_dvd_a ap_eq,
      have a'_dvd_a : a' ∣ a,
      {
        rw eq_a_bis,
        exact dvd_mul_left _ _,
      },
      have eq_b_bis : b = gcd a b * b', from nat.eq_mul_of_div_eq_right gcd_dvd_b bp_eq,
      have b'_dvd_b : b' ∣ b,
      {
        rw eq_b_bis,
        exact dvd_mul_left _ _,
      },
      have a_dvd_n : a ∣ n, from h.right.right.right.right.left,
      have a'_dvd_n : a' ∣ n, from gcd_dvd_trans a'_dvd_a a_dvd_n, 
      have b'_dvd_n : b' ∣ n, from gcd_dvd_trans b'_dvd_b b_dvd_n, 
      have eq2 : (b / (gcd a b)) * gcd a b = b, from nat.div_mul_cancel gcd_dvd_b,
      --have eq2_bis : gcd a b * a / (gcd a b) = a, from  nat.mul_comm (nat.div_mul_cancel gcd_dvd_a),
      have eq_b : d*b' = b, 
      {
        calc
           d*b' =  b : by rw [nat.mul_comm,d_eq, bp_eq, eq2]
      },
       have eq_a : d*a' = a,
      {
        calc
           d*a' =  gcd a b * a' : by rw d_eq
           ...  =  gcd a b * (a / (gcd a b))  : by rw ap_eq
           ...  =   a / gcd a b * gcd a b  : by rw nat.mul_comm
           ...  =  a  : by rw nat.div_mul_cancel gcd_dvd_a
      },
    cases h1 with cda' cdb',
    {
      have cdba : coprime (d*b') a', 
      {
          have cbpap : coprime b' a',
          {
              have b_gr_0 : b > 0, 
              {
                 rw pos_iff_ne_zero,
                 exact h.right.left,
              },
              have gcd_gr_0 : gcd b a > 0, from nat.gcd_pos_of_pos_left a b_gr_0,
              have cop_fractions : coprime (b /gcd b a) (a / gcd b a), from nat.coprime_div_gcd_div_gcd gcd_gr_0,
              have cop_fractions_2 : coprime (b /gcd a b) (a / gcd a b), from eq.subst (gcd_comm b a) cop_fractions,
              have cop_fractions_3 : coprime b' (a / gcd a b), from eq.subst bp_eq cop_fractions_2,
              exact eq.subst ap_eq cop_fractions_3,
          },
          exact coprime.mul cda' cbpap,
      },
      have cba : coprime b a', from eq.subst eq_b cdba,
      have ba'_dvd_n : b*a' ∣ n, from coprime_dvd_of_dvd_mul b_dvd_n a'_dvd_n cba,
      have  eq3 : b*a' = m,
      {
        calc
           b*a'    =  b * (a / gcd a b) : by rw ap_eq
               ... =  (b * a) / gcd a b :  by rw nat.mul_div_assoc b gcd_dvd_a 
               ... =  a * b / gcd a b : by rw nat.mul_comm
               ... = m : by rw m_def 
      },
      exact eq.subst eq3 ba'_dvd_n,

    },
    {
     have cdba : coprime (d*a') b', 
      {
          have capbp : coprime a' b',
          {
              have b_gr_0 : b > 0, 
              {
                 rw pos_iff_ne_zero,
                 exact h.right.left,
              },
              have gcd_gr_0 : gcd a b > 0, from nat.gcd_pos_of_pos_right a b_gr_0,
              have cop_fractions : coprime (a / gcd a b) (b /gcd a b), from nat.coprime_div_gcd_div_gcd gcd_gr_0,
              have cop_fractions_2 : coprime a' (b / gcd a b), from eq.subst ap_eq cop_fractions,
              exact eq.subst bp_eq cop_fractions_2,

          },
          exact coprime.mul cdb' capbp,
      },
      have cba : coprime a b', from eq.subst eq_a cdba,
      have ba'_dvd_n : a*b' ∣ n, from coprime_dvd_of_dvd_mul a_dvd_n b'_dvd_n cba,
      have  eq3 : a*b' = m,
      {
        calc
           a*b'    =  a * (b / gcd a b) : by rw bp_eq
               ... =  (a * b) / gcd a b :  by rw nat.mul_div_assoc a gcd_dvd_b
               ... = m : by rw m_def 
      },
      exact eq.subst eq3 ba'_dvd_n,
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

#print notation ∣
#print has_dvd.dvd
variables a b c : ℕ 



variable gcd_dvd_b : (gcd a b) ∣ b
variable b_diff_0 : (b≠0)
#check  nat.div_mul_cancel gcd_dvd_b
#check  nat.div_mul_cancel gcd_dvd_b

variable a' : ℕ
variable (adiff0: (a' > 0))
variable (advdb: (a' ∣ a))
variable (gcddivides : (gcd a b ∣ a))
variable (eq:  a/(gcd a b) = a')
#check nat.div_eq_iff_eq_mul_right adiff0 advdb 
#check nat.eq_mul_of_div_eq_right advdb eq
#check nat.eq_mul_of_div_eq_right gcddivides eq
#print coprime
#print notation ∣ 
#check has_dvd.dvd 


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
