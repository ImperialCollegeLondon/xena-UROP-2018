import data.nat.prime
import data.nat.modeq data.int.modeq
import analysis.real
import tactic.norm_num
import algebra.group_power
import data.int.basic
import M3P14.order
import chris_hughes_various.zmod
import M3P14.lqr
import M3P14.phi

open nat

-- Questions:
-- Compute 210 449 and 605/617 using quadratic reciprocity.
--  449 and 617 are both prime).
-- TODO: how to prove it using quadratic reciprocity?


theorem ls_3_449 (oddprime_449 : (prime 449 ∧ 449 ≠ 2)) : legendre_sym 3 oddprime_449 = -1 :=
begin
    have oddprime_3 : prime 3 ∧ 3 ≠ 2, from ⟨prime_three, by norm_num⟩,
    have b2: (legendre_sym 3 oddprime_449) = (legendre_sym 449 oddprime_3) * 1, from eq.subst (show (-1:ℤ)^(((3-1)/2)*((449-1)/2)) = 1, by norm_num) (law_of_quadratic_reciprocity' oddprime_3 oddprime_449),
    rw b2,
    simp, 
    rw legendre_sym_refl 449 2 oddprime_3, 
    rw legendre_sym_supplementary_laws,
    norm_num,
    unfold int.modeq,
    norm_num,
end

theorem ls_5_449 (H : prime 449 ∧ 449 ≠ 2) : legendre_sym 5 H = 1 := 
begin 
    have prime_5 : prime 5 ∧ 5 ≠ 2, sorry,
    rw (show (legendre_sym 5 H) = (legendre_sym 449 prime_5) * (-1)^(((5-1)/2)*((449-1)/2)), from law_of_quadratic_reciprocity' _ _),
    norm_num,
    have : 449 ≡ -1 [ZMOD 5], by norm_num [int.modeq],
    rw [legendre_sym_refl _ _ prime_5 this, legendre_neg_one],
    norm_num,
end

theorem ls_7_449 (H : prime 449 ∧ 449 ≠ 2) : legendre_sym 7 H = 1 := 
begin
   have prime_7 : prime 7 ∧ 7 ≠ 2, sorry,
    rw (show (legendre_sym 7 H) = (legendre_sym 449 prime_7) * (-1)^(((7-1)/2)*((449-1)/2)), from law_of_quadratic_reciprocity' _ _),
    norm_num,
    have : 449 ≡ 1 [ZMOD 7], by unfold int.modeq; norm_num, 
    rw [legendre_sym_refl _ _ prime_7 this, legendre_one],
end

theorem ls_5_617 (H : prime 617 ∧ 617 ≠ 2) : legendre_sym 5 H = -1 := 
begin
    have prime_5 : prime 5 ∧ 5 ≠ 2, sorry,
    rw (show (legendre_sym 5 H) = (legendre_sym 617 prime_5) * (-1)^(((5-1)/2)*((617-1)/2)), from law_of_quadratic_reciprocity' _ _),
    norm_num,
    have : 617 ≡ 2 [ZMOD 5], by unfold int.modeq; norm_num, 
    rw [legendre_sym_refl _ _ prime_5 this, legendre_sym_supplementary_laws],
    norm_num,
end

theorem ls_11_617 (H : prime 617 ∧ 617 ≠ 2) : legendre_sym 11 H = 1 := 
begin
    have prime_11 : prime 11 ∧ 11 ≠ 2, sorry,
    rw (show (legendre_sym 11 H) = (legendre_sym 617 prime_11) * (-1)^(((11-1)/2)*((617-1)/2)), from law_of_quadratic_reciprocity' _ _),
    norm_num,
    have : 617 ≡ 1 [ZMOD 11], by unfold int.modeq; norm_num, 
    rw [legendre_sym_refl _ _ prime_11 this, legendre_one],
end

theorem q1 (H1 : prime 449 ∧ 449 ≠ 2) (H2 : prime 617 ∧ 617 ≠ 2) : ((legendre_sym 210 H1) = (-1 : ℤ)) ∧ ((legendre_sym 605 H2) = (-1: ℤ) ) :=
begin
    split,
    have h : (-1 : ℤ)^((449^2 -1)/8) = 1, by norm_num,
    have h13: legendre_sym 2 H1 = (-1:ℤ)^((449^2-1)/8), from legendre_sym_supplementary_laws H1, 
    have a1: legendre_sym 2 H1 = 1, from eq.trans h13 h,  
    have eq_210 : (210 : ℤ) = (2 : ℤ)  * (3 : ℤ) * (5 : ℤ) * (7 : ℤ), by norm_num,
    rw [eq_210, legendre_sym_mul, legendre_sym_mul, legendre_sym_mul, ls_7_449 H1, ls_5_449 H1, ls_3_449 H1, a1],
    norm_num,
    have eq_605 : (605 : ℤ) = (5 : ℤ)  * (11 : ℤ) * (11 : ℤ), by norm_num,
    rw [eq_605, legendre_sym_mul, legendre_sym_mul,ls_5_617, ls_11_617],
    norm_num,
end 

-- Find all 6 primitive roots modulo 19.
theorem q2a : ∃ A : set ℕ, ∀ x : ℕ, primitive_root x 19 ↔ x ∈ A := sorry

-- Show that if n is odd and a is a primitive root mod n, then a is a primitive root mod 2n if a is odd, and a + n is a primitive root mod 2n if a is even. 
-- [HINT: Φ(2n) = Φ(n) when n is odd.]
theorem q2b {a n : ℕ} (h_odd : gcd 2 n = 1) (hp : primitive_root a n) : (gcd 2 a = 1 → primitive_root a (2*n)) ∧ (gcd 2 a = 0 → primitive_root (a + n) (2*n)) := sorry

-- Let p be a prime and let a be a primitive root mod p. 
-- Show that a is also a primitive root mod p² if, and only if, a^p−1 is not congruent to 1 mod p².
-- [HINT: what is the order of a mod p? What does this say about the order of a mod p²?]
--set_option pp.proofs true
theorem q3 {a p : ℕ} (hp : prime p) (h1: coprime a p) (h2 : coprime a (p^2)) (hq : primitive_root a p h1) :
primitive_root a (p^2) h2 ↔ ¬(a^(p-1) ≡ 1 [MOD (p^2)]) :=
    begin
    apply iff.intro,
    {
        intro j1, unfold primitive_root at hq j1,
        have j2: phi (p^2) = p^1*(p-1), from power_p_phi p 2 hp,
        have j3: p^1*(p-1) = p*(p-1), by simp,
        have j4: phi (p^2) = p*(p-1), from eq.subst j2.symm j3,
        have j5: order_of a (p^2) h2 = p*(p-1), from eq.subst j1.symm j4,
        assume j6: a^(p-1) ≡ 1 [MOD (p^2)],
        have j7: order_of a (p^2) h2 ∣ (p-1), from order_div a (p^2) (p-1) h2 j6,
        have j8: p*(p-1) ∣ (p-1), from eq.subst j5 j7,
        have j9: ¬ p*(p-1) ∣ (p-1), from mt (le_of_dvd (nat.sub_pos_of_lt hp.gt_one)) 
          (not_le_of_gt ((lt_mul_iff_one_lt_left (nat.sub_pos_of_lt hp.gt_one)).2 hp.gt_one)),
        from absurd j8 j9,
    },

    {
        intro j1, unfold primitive_root at hq, unfold primitive_root,
        have j2: phi (p^2) = p^1*(p-1), from power_p_phi p 2 hp,
        have j3: order_of a (p^2) h2 ∣ phi (p^2), from order_div_phi_n a (p^2) h2,
        have j4: order_of a (p^2) h2 ∣ p^1*(p-1), from eq.subst j2 j3,
        have j5: a ^ order_of a (p^2) h2 ≡ 1 [MOD (p^2)], from pow_order_eq_one a (p^2) h2,
        have j6: a ^ order_of a p h1 ≡ 1 [MOD p], from sorry,
        sorry,
    }
end 

-- Let p be a prime, and let a be an integer not divisible by p. 
-- Show that the equation x^d ≡ a (mod p) has a solution if, and only if, a^(p−1/(d,p−1)) ≡ 1 (mod p). 
-- Show further that if this is the case then this equation has (d, p − 1) solutions mod p.
-- [HINT: what happens when you fix a primitive root g mod p, and take the discrete log of the equation x^d ≡ a (mod p)?]
theorem q4 (p a x d : ℕ) (hp : prime p) : x^d ≡ a [MOD p] ↔ a^(p-1/(gcd d (p-1))) ≡ 1 [MOD p] := sorry

-- Let p be an odd prime different from 7. 
-- Show that 7 is a square mod p if, and only if, p is congruent to 1, 3, 9, 19, 25 or 27 modulo 28.
-- [HINT: use quadratic reciprocity to relate 7/p to p/7.]
theorem q5 (p x : ℕ) (hp: prime p) (hq: p ≠ 7) : x^2 ≡ 7 [MOD p] ↔ (p ≡ 1 [MOD 28] ∨ p ≡ 3 [MOD 28] ∨  p ≡ 9 [MOD 28] ∨ p ≡ 19 [MOD 28] ∨  p ≡ 25 [MOD 28] ∨ p ≡ 25 [MOD 28]) := sorry

-- Let n and m be relatively prime. Show that every element of (ℤ/nmℤ)^x has order dividing the least common multiple of Φ(n) and Φ(m).
--theorem q6a {n m : ℕ} (hp : gcd m n = 1) : := sorry  

-- Show that if n and m are relatively prime, then ℤ/nmℤ has a primitive root if, and only if, both ℤ/nℤ and ℤ/mℤ have primitive roots, and (Φ(n), Φ(m)) = 1.
-- When can this happen?
--theorem q6b (n m : ℕ) (hp : gcd m n = 1) := sorry 

-- Suppose a is a primitive root modulo n. Show that a^d is also a primitive root modulo n for all d such that (d, Φ(n)) = 1.
-- [Hint: show that there exists k such that (a^d)^k is equal to a.]
theorem q7 {a n : ℕ} (hp : primitive_root a n) : ∀ d : ℕ, gcd d (phi n) = 1 → primitive_root (a^d) n := sorry 

-- Show that if p is a prime congruent to ±1 mod 24 then none of 2, 3, 4, 6is a primitive root modulo p.
-- [Hint: show that 2 and 3 are squares mod p.]
theorem q8 (p : ℕ) (hp : prime p) : (p ≡ 1 [ZMOD 24] ∨ p ≡ -1 [ZMOD 24])  := sorry