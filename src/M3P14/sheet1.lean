import data.nat.gcd
import data.nat.modeq
import data.nat.prime
import tactic.norm_num
import data.nat.gcd
--import data.set 

open classical 

namespace nat


-- Show that for a, b, d integers, we have (da, db) = d(a,b).
--TODO: change ℕ to ℤ
theorem q1a (a b d : ℤ) : int.gcd (d*a) (d*b) = d * (int.gcd a b) := gcd_mul_left d a b

-- Let a, b, n integers, and suppose that n|ab. Show that n/(a,b) divides b.
--TODO: change ℕ to ℤ
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

-- Find, with proof, all solutions to the linear diophantine equation 110x + 68y = 14.
theorem q2b : ∃ A : set (ℤ×ℤ), ∀ x y : ℤ, (110*x + 68*y = 14 ↔ (x,y) ∈ A ):= 
begin
apply exists.intro ∅,  --the answer is not ∅ 
assume x y,
apply iff.intro,
{

    sorry,
},
{
  intro h,
  exact false.elim ‹(x, y) ∈ (∅ : set (ℤ×ℤ))›,
}
end


-- Find a multiplicative inverse of 31 modulo 132.
theorem q2c : ∃ x : ℤ, 31*x % 132 = 1 := 
    ⟨115, by norm_num⟩

-- Find an integer congruent to 3 mod 9 and congruent to 1 mod 49.
theorem q2d : ∃ x : ℤ, x % 9 = 3 → x % 49 = 1 :=  
    ⟨-195, by norm_num⟩


-- Find, with proof, the smallest nonnegative integer n such that n = 1 (mod 3), n = 4 (mod 5), and n = 3 (mod 7).
theorem extended_chinese_remainder {p q r : ℕ} (co : coprime p q ∧ coprime q r ∧ coprime r p) (a b c: ℕ) :
    {k // k ≡ a [MOD p] ∧ k ≡ b [MOD q] ∧ k ≡ c[MOD r]} := sorry 

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
--TODO: change ℕ to ℤ
theorem q3 : ∀ m n : ℕ, ∃! d : ℕ, ∀ x : ℤ, gcd m n = d → d ∣ m → d ∣ n → x ∣ m → x ∣ n → x ∣ d
                                    := sorry


-- Let a and b be nonzero integers. Show that there is a unique positive integer m with the following two properties:
--      - a and b divide m, and
--      - if n is any number divisible by both a and b, then m|n.
-- The number m is called the least common multiple of a and b.  
 --TODO: change ℕ to ℤ
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
--theorem gcd_eq_pair_number (a b : ℕ) : ∃ x y : ℤ,  gcd a b = x*a + b*y := sorry 
-- theorem gcd_iff_pair_number (a b d : ℕ) : gcd a b = d ↔ ∃ x y : ℤ, x*a + b*y = d := sorry
theorem coprime_dvd_of_dvd_mul {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : coprime a b) : 
    a*b ∣ c := sorry


theorem q4a : ∀ a b : ℕ, ∃! m : ℕ, ∀ n : ℕ, a ≠ 0 ∧ b ≠ 0 ∧   
                                a ∣ m ∧ b ∣ m ∧ a ∣ n ∧ b ∣ n → m ∣ n
                                := 
begin 
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
  have eq2 : (b / (gcd a b)) * gcd a b = b, from nat.div_mul_cancel gcd_dvd_b,
  
  have eq_a : d*a' = a,
      {
        calc
           d*a' =  gcd a b * a' : by rw d_eq
           ...  =  gcd a b * (a / (gcd a b))  : by rw ap_eq
           ...  =   a / gcd a b * gcd a b  : by rw nat.mul_comm
           ...  =  a  : by rw nat.div_mul_cancel gcd_dvd_a
      },
  have eq_b : d*b' = b,
   {
        calc
           d*b' =  b : by rw [nat.mul_comm,d_eq, bp_eq, eq2]
   },
  have da'_dvd_n: d*a' ∣ n, from eq.subst (eq.symm eq_a) a_dvd_n,
  have db'_dvd_n: d*b' ∣ n, from eq.subst (eq.symm eq_b) b_dvd_n,
  have gcd_pos: gcd a b > 0, from gcd_pos_of_pos_left b ((nat.pos_iff_ne_zero).mpr h.left),
  have middlestep: a' * gcd a b ∣ n / d * gcd a b, 
  {
    rw mul_comm,
    rw ← d_eq,
    have d_dvd_n: d ∣ n, from dvd_of_mul_right_dvd da'_dvd_n,
    rwa nat.div_mul_cancel d_dvd_n, 

  },
  have a'_dvd_n_dvd_d: a' ∣ n/d, from dvd_of_mul_dvd_mul_right gcd_pos middlestep,
  have middlestep2: b' * gcd a b ∣ n / d * gcd a b, 
  {
    rw mul_comm,
    rw ← d_eq,
    have d_dvd_n: d ∣ n, from dvd_of_mul_right_dvd db'_dvd_n,
    rwa nat.div_mul_cancel d_dvd_n, 

  },
  have b'_dvd_n_dvd_d: b' ∣ n/d, from dvd_of_mul_dvd_mul_right gcd_pos middlestep2,
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
  have apbp_dvd_n_dvd_d: a'*b' ∣ n/d, from coprime_dvd_of_dvd_mul a'_dvd_n_dvd_d b'_dvd_n_dvd_d capbp,
  have : a'*b'*d ∣ n,
  {
    have d_gr_zero : d > 0, from (eq.subst (eq.symm d_eq) gcd_pos),
    
    rw ← nat.mul_div_cancel n d_gr_zero,
    have : a' * b' * d ∣ (n / d) * d, from mul_dvd_mul_right apbp_dvd_n_dvd_d d,
    have : a' * b' * d ∣ d * (n / d), from eq.subst (mul_comm (n / d) d) this, 
    have d_dvd_n: d ∣ n, from dvd_of_mul_right_dvd da'_dvd_n,
    have : a' * b' * d ∣ d * n / d, from  eq.subst (eq.symm (nat.mul_div_assoc d d_dvd_n)) this,
    exact eq.subst (mul_comm d n) this,
  },
have  eq3 : a'*b'*d = m,
      {
        calc
           a'*b'*d    =  (a/gcd a b) * ((b/gcd a b) * gcd a b) : by rw [ap_eq, bp_eq, d_eq]
               ... = (a/gcd a b) * (gcd a b * (b/gcd a b)) : by rw nat.mul_comm 
               ... = (a/gcd a b) * (gcd a b * b/gcd a b) : by rw ←nat.mul_div_assoc (gcd a b) gcd_dvd_b
               ... =  (a/gcd a b) * (b * gcd a b /gcd a b) :  by rw nat.mul_comm (gcd a b) b 
               ... = (a/gcd a b) * b : by rw nat.mul_div_cancel b gcd_pos 
               ... =  b * (a / gcd a b) : by rw nat.mul_comm 
               ... =  b * a / gcd a b : by rw nat.mul_div_assoc b gcd_dvd_a 
               ... = m : by rw [mul_comm,m_def] 
      },
  rwa ←eq3,
},
{
let p := lcm a b,
let q := lcm a b,
-- p divides q and q divides p => p = q
}
end
#check lcm 
-- Show that the least common multiple of a and b is given by |ab|/(a,b)
-- TODO: need to change ℕ to ℤ and use abs(a*b)
theorem q4b : ∀ a b : ℕ, lcm a b = a*b/(gcd a b) := sorry
/-begin
  intros a b,
  exact gcd_mul_lcm a b,
  sorry
end
-/

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
