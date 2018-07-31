import data.nat.prime
import data.nat.modeq data.int.modeq
import analysis.real
import tactic.norm_num
import algebra.group_power
import data.int.basic
import M3P14.order
import chris_hughes_various.zmod
import M3P14.lqr

open nat

-- Questions:
-- Compute 210 449 and 605/617 using quadratic reciprocity.
--  449 and 617 are both prime).
-- TODO: how to prove it using quadratic reciprocity?

lemma LQR_1 {p q : ℕ} (hp : (prime p ∧ p ≠ 2)) (hq : (prime q ∧ q ≠ 2)) : (legendre_sym p hq) = (legendre_sym q hp) * (-1)^(((p-1)/2)*((q-1)/2)) := sorry 


lemma legendre_sym_3 (oddprime_449 : (prime 449 ∧ 449 ≠ 2)) : legendre_sym 3 oddprime_449 = -1 :=
begin
    have oddprime_3 : prime 3 ∧ 3 ≠ 2, sorry,
    have b2: (legendre_sym 3 oddprime_449) = (legendre_sym 449 oddprime_3) * 1, from eq.subst (show (-1:ℤ)^(((3-1)/2)*((449-1)/2)) = 1, by norm_num) (LQR_1 oddprime_3 oddprime_449),
    rw b2,
    simp, 
    rw legendre_sym_refl 449 2 oddprime_3, 
    rw legendre_sym_supplementary_laws,
    norm_num,
    have : 449 ≡ 2 [MOD 3], sorry,-- by norm_num,
    exact (int.modeq.coe_nat_modeq_iff _ _ _).mpr this,
end

lemma legendre_sym_5 (H1 : prime 449 ∧ 449 ≠ 2) : legendre_sym 5 H1 = 1 := 
begin 
    have prime_5 : prime 5 ∧ 5 ≠ 2, sorry,

    have h34 : (legendre_sym 5 H1)*(legendre_sym 449 prime_5) = (-1: ℤ)^(((5-1)/2)*((449-1)/2)), from law_of_quadratic_reciprocity prime_5 H1,
    have h35 : (-1 : ℤ)^(((5-1)/2)*((449 -1)/2)) = 1, by norm_num,
 
    have h36 : 449-4 = 5*89, by norm_num,
    have h37 : 5 ∣ 5*89, from dvd_mul_right 5 89,
    have h38 : 5 ∣ (449-4), from eq.subst h36 h37,
    have h39 : (5:ℤ) ∣ (449-4), sorry,
    --have h40: 4 ≡ 449 [MOD 5], from nat.modeq.modeq_of_dvd h39,
    have h41 : 449 ≡ 4 [MOD 5], from nat.modeq.symm (nat.modeq.modeq_of_dvd h39),
    have h42 : legendre_sym 449 prime_5 = legendre_sym 4 prime_5, from legendre_sym_refl 449 4 prime_5 ((int.modeq.coe_nat_modeq_iff _ _ _).mpr h41),
    have h43 : 4-2^2=5*0, by norm_num,
    have h44 : 5 ∣ 5*0, from dvd_mul_right 5 0,
    have h45 : 5 ∣ 4-2^2, from eq.subst h43 h44,
    have h46 : (5:ℤ) ∣ 4-2^2, sorry,
    have h47 : 4 ≡ 2^2 [MOD 5], from nat.modeq.modeq_of_dvd h46,
    have : quadratic_res 4 5, 
    begin 
    unfold quadratic_res,
    existsi 2,
    exact (int.modeq.coe_nat_modeq_iff _ _ _).mpr h47,
    end,

    have h49: legendre_sym 4 prime_5 = 1,
    begin
        unfold legendre_sym,
        split_ifs,
        refl,
        exfalso,/-
        apply h_1,
        split,
        exact this,
        exact dec_trivial,-/
        sorry,
    end,
    

    have g27 : (legendre_sym 5 H1)*(legendre_sym 449 prime_5) = 1, from eq.trans h34 h35,
    have g28 : (legendre_sym 5 H1)*(legendre_sym 4 prime_5) = 1, from eq.subst h42 g27,
    have g29 : (legendre_sym 5 H1)*1 = 1, sorry, --from eq.subst h49 g28,
    have g33 : (legendre_sym 5 H1) = (legendre_sym 5 H1)*1, by rw mul_one,
    exact eq.trans g33 g29, 
end

lemma legendre_sym_7_bis (H1 : prime 449 ∧ 449 ≠ 2) : legendre_sym 7 H1 = 1 := 
begin
    rw legendre_sym,
    split_ifs,
    refl,
    rw not_and at h,
    --have : ¬¬↑449 ∣ 7, from h h_1,
    sorry,
end

lemma legendre_sym_7 (H1 : prime 449 ∧ 449 ≠ 2) : legendre_sym 7 H1 = 1 := 
begin 

    have prime_7 : prime 7 ∧ 7 ≠ 2, sorry,

    have h50 : (legendre_sym 7 H1)*(legendre_sym 449 prime_7) = (-1: ℤ)^(((7-1)/2)*((449-1)/2)), from law_of_quadratic_reciprocity prime_7 H1,
    have h51 : (-1: ℤ)^(((7-1)/2)*((449)-1)/2) = 1, by norm_num,
 
 
    have h52 : 449-1 = 7*64, by norm_num,
    have h53 : 7 ∣ 7*64, from dvd_mul_right 7 64,
    have h54 : 7 ∣ (449-1), from eq.subst h52 h53,
    have h55 : (7:ℤ) ∣ (449-1), sorry,
    --have h56: 1 ≡ 449 [MOD 7], from nat.modeq.modeq_of_dvd h55,
    have h57 : 449 ≡ 1 [MOD 7], from nat.modeq.symm (nat.modeq.modeq_of_dvd h55),
    have h58 : legendre_sym 449 prime_7 = legendre_sym 1 prime_7, from legendre_sym_refl 449 1 prime_7 ((int.modeq.coe_nat_modeq_iff _ _ _).mpr h57),
    have h59 : 1-1^2 = 7*0, by norm_num,
    have h60 : 7 ∣ 7*0, from dvd_mul_right 7 0,
    have h61 : 7 ∣ 1-1^2, from eq.subst h59 h60,
    have h62 : (7:ℤ) ∣ 1-1^2, sorry,
    have h63 : 1 ≡ 1^2 [MOD 7], from nat.modeq.modeq_of_dvd h62,

    have : quadratic_res 1 7, 
    begin 
        unfold quadratic_res,
        existsi 1,
        exact (int.modeq.coe_nat_modeq_iff _ _ _).mpr h63,
    end,

    have h64: legendre_sym 1 prime_7 = 1, sorry, /-
    begin
        unfold legendre_sym,
        split_ifs,
        refl,
        exfalso,
        apply H1,
        split,
        exact this,
        exact dec_trivial,
    end,-/

    have j27 : (legendre_sym 7 H1)*(legendre_sym 449 prime_7) = 1, from eq.trans h50 h51,
    have j28 : (legendre_sym 7 H1)*(legendre_sym 1 prime_7) =1, from eq.subst h58 j27,
    have j29 : (legendre_sym 7 H1)*1 = 1, sorry,
    have j30 : 1*(legendre_sym 7 H1) = legendre_sym 7 H1, from one_mul (legendre_sym 7 H1),
    have j31 : (legendre_sym 7 H1)*1 = 1*(legendre_sym 7 H1), from mul_comm (legendre_sym 7 H1) 1,  
    have j32 : (legendre_sym 7 H1)*1 = (legendre_sym 7 H1), from eq.trans j31 j30,
    have j33 : (legendre_sym 7 H1) = (legendre_sym 7 H1)*1, from eq.symm j32,
    exact eq.trans j33 j29,

end
 


theorem q1 (H1 : prime 449 ∧ 449 ≠ 2) (H2 : prime 617 ∧ 617 ≠ 2) : ((legendre_sym 210 H1) = (-1 : ℤ)) ∧ ((legendre_sym 605 H2) = (-1: ℤ) ) :=
begin
    split,
    have h : (-1 : ℤ)^((449^2 -1)/8) = 1, by norm_num,
    have h13: legendre_sym 2 H1 = (-1:ℤ)^((449^2-1)/8), from legendre_sym_supplementary_laws H1, 
    have a1: legendre_sym 2 H1 = 1, from eq.trans h13 h,  
    have eq_210 : (210 : ℤ) = (2 : ℤ)  * (3 : ℤ) * (5 : ℤ) * (7 : ℤ), by norm_num,
    rw [eq_210, legendre_sym_mul, legendre_sym_mul, legendre_sym_mul, legendre_sym_7 H1, legendre_sym_5 H1, legendre_sym_3 H1, a1],
    norm_num,
    -----
    /- goal legendre_sym 605 H2 = -1 -/

    sorry,

end 


/-
set_option trace.check true
example (H1 : prime 449 ∧ 449 ≠ 2) : legendre_sym 210 H1 = -1 :=
begin
  have H : 210 = 2 * 3 * 5 * 7, norm_num,
  rw H, -- goal now ⊢ legendre_sym (2 * 3 * 5 * 7) H1 = -1
  rw legendre_sym_mul,
  rw legendre_sym_mul,
  rw legendre_sym_mul,
  -- goal now legendre_sym 2 H1 * legendre_sym 3 H1 * legendre_sym 5 H1 * legendre_sym 7 H1 = -1
  sorry
end
-/
 
-- Find all 6 primitive roots modulo 19.
theorem q2a : ∃ A : set ℕ, ∀ x : ℕ, primitive_root x 19 ↔ x ∈ A := sorry

-- Show that if n is odd and a is a primitive root mod n, then a is a primitive root mod 2n if a is odd, and a + n is a primitive root mod 2n if a is even. 
-- [HINT: Φ(2n) = Φ(n) when n is odd.]
theorem q2b {a n : ℕ} (h_odd : gcd 2 n = 1) (hp : primitive_root a n) : (gcd 2 a = 1 → primitive_root a (2*n)) ∧ (gcd 2 a = 0 → primitive_root (a + n) (2*n)) := sorry

-- Let p be a prime and let a be a primitive root mod p. 
-- Show that a is also a primitive root mod p² if, and only if, a^p−1 is not congruent to 1 mod p².
-- [HINT: what is the order of a mod p? What does this say about the order of a mod p²?]
theorem q3 {a p : ℕ} (hp : prime p) (hq : primitive_root a p) : primitive_root a (p*p) ↔ ¬(a^(p-1) ≡ 1 [MOD (p*p)]) := sorry

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