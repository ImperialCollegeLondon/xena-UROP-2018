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
theorem q1 (H1 : prime 449) (H2 : prime 617) : ((legendre_sym 210 H1) = (-1 : ℤ)) ∧ ((legendre_sym 605 H2) = (-1: ℤ) ) :=
begin
split,
have h1: 210 = 2*105, refl,
have h2: legendre_sym 210 H1 = legendre_sym 210 H1, refl, 
have h3: legendre_sym 210 H1 = legendre_sym (2*105) H1, from eq.subst h1 h2, 
have h4: legendre_sym (2*105) H1 = (legendre_sym 2 H1)*(legendre_sym 105 H1), from legendre_sym_mul 2 105 H1,
have h5: 105 = 3*35, refl,
have h6: legendre_sym 105 H1 = legendre_sym 105 H1, refl,
have h7: legendre_sym 105 H1 = legendre_sym (3*35) H1, from eq.subst h5 h6, 
have h8: legendre_sym (3*35) H1 = (legendre_sym 3 H1)*(legendre_sym 35 H1), from legendre_sym_mul 3 35 H1,
have h9: 35 = 5*7, refl,
have h10: legendre_sym 35 H1 = legendre_sym 35 H1, refl,
have h11: legendre_sym 35 H1 = legendre_sym (5*7) H1, from eq.subst h9 h10,
have h12: legendre_sym (5*7) H1 = (legendre_sym 5 H1)*(legendre_sym 7 H1), from legendre_sym_mul 5 7 H1,

have h : (-1: ℤ)^((449^2 -1)/8) = 1, by norm_num,

have h13: legendre_sym 2 H1 = (-1:ℤ)^((449^2-1)/8), from legendre_sym_supplementary_laws H1, 
have a1: legendre_sym 2 H1 = 1, from eq.trans h13 h,  

have prime_3 : prime 3, sorry,
have h14: (legendre_sym 3 H1)*(legendre_sym 449 prime_3) = (-1: ℤ)^(((3-1)/2)*((449-1)/2)), from (law_of_quadratic_reciprocity prime_3 H1),
have h15: (-1: ℤ)^(((3-1)/2)*((449-1)/2)) = 1, by norm_num,

have h16: 449-2 = 3*149, by norm_num,
have h17: 3 ∣ 3*149, from dvd_mul_right 3 149,
have h18: 3 ∣ (449-2), from eq.subst h16 h17,
have h19: (3:ℤ) ∣ (449-2), sorry,
have h20: 2 ≡ 449 [MOD 3], from nat.modeq.modeq_of_dvd h19,
have h21: 449 ≡ 2 [MOD 3], from nat.modeq.symm h20,
have h22: legendre_sym 449 prime_3 = legendre_sym 2 prime_3, from legendre_sym_refl 449 2 prime_3 h21,
have h23: (-1: ℤ)^((3^2-1)/8) = -1, by norm_num,
have h24: legendre_sym 2 prime_3 = (-1: ℤ)^((3^2-1)/8), from legendre_sym_supplementary_laws prime_3,
have h25: legendre_sym 2 prime_3 = -1, from eq.trans h24 h23,
have h26: legendre_sym 449 prime_3 = -1, from eq.trans h22 h25, 
have h27: (legendre_sym 3 H1)*(legendre_sym 449 prime_3) = 1, from eq.trans h14 h15,
have h28: (legendre_sym 3 H1)*(-1) = 1, from eq.subst h26 h27,
have h29: 1=(legendre_sym 3 H1)*(-1), from eq.symm h28,
have h30: (-1:ℤ) ≠ (0:ℤ) := dec_trivial,
have h31: 1/(-1 : ℤ) = legendre_sym 3 H1, sorry, --from int.basic.div_eq_of_eq_mul_left h30 h29,
have h32: -1 = 1/(-1:ℤ), by norm_num,
have h33: -1 = legendre_sym 3 H1, from eq.trans h32 h31,
have a2: legendre_sym 3 H1 = -1, from eq.symm h33,


------

have prime_5 : prime 5, sorry,

have h34: (legendre_sym 5 H1)*(legendre_sym 449 prime_5) = (-1: ℤ)^(((5-1)/2)*((449-1)/2)), from law_of_quadratic_reciprocity prime_5 H1,
have h35: (-1: ℤ)^(((5-1)/2)*((449 -1)/2)) = 1, by norm_num,

have h36: 449-4 = 5*89, by norm_num,
have h37: 5 ∣ 5*89, from dvd_mul_right 5 89,
have h38: 5 ∣  (449-4), from eq.subst h36 h37,
have h39: (5:ℤ) ∣  (449-4), sorry,
have h40: 4 ≡ 449 [MOD 5], from nat.modeq.modeq_of_dvd h39,
have h41: 449 ≡ 4 [MOD 5], from nat.modeq.symm h40,
have h42: legendre_sym 449 prime_5 = legendre_sym 4 prime_5, from legendre_sym_refl 449 4 prime_5 h41,
have h43: 4-2^2=5*0, by norm_num,
have h44: 5 ∣ 5*0, from dvd_mul_right 5 0,
have h45: 5 ∣ 4-2^2, from eq.subst h43 h44,
have h46: (5:ℤ) ∣ 4-2^2, sorry,
have h47: 4 ≡ 2^2 [MOD 5], from nat.modeq.modeq_of_dvd h46,
have : quadratic_res 4 5, 
begin 
unfold quadratic_res,
existsi 2,
exact h47,
end,

have h49: legendre_sym 4 prime_5 = 1,
begin
unfold legendre_sym,
split_ifs,
refl,
exfalso,
apply h_1,
split,
exact this,
exact dec_trivial,
end,

have g27: (legendre_sym 5 H1)*(legendre_sym 449 prime_5)= 1, from eq.trans h34 h35,
have g28: (legendre_sym 5 H1)*(legendre_sym 4 prime_5) =1, from eq.subst h42 g27,
have g29: (legendre_sym 5 H1)*1 = 1, sorry,
--have g30: 1*(legendre_sym 5 H1) = legendre_sym 5 H1, from one_mul (legendre_sym 5 H1),
--have g31: (legendre_sym 5 H1)*1 = 1*(legendre_sym 5 H1), from mul_comm (legendre_sym 5 H1) 1,  
--have g32: (legendre_sym 5 H1)*1=(legendre_sym 5 H1), from eq.trans g31 g30,
--have g33: (legendre_sym 5 H1)=(legendre_sym 5 H1)*1, from eq.symm g32,
have a3: legendre_sym 5 H1 = 1, from eq.subst (mul_one (legendre_sym 5 H1)) g29,


-----

have prime_7 : prime 7, sorry,

have h50: (legendre_sym 7 H1)*(legendre_sym 449 prime_7) = (-1: ℤ)^(((7-1)/2)*((449-1)/2)), from law_of_quadratic_reciprocity prime_7 H1,
have h51: (-1: ℤ)^(((7-1)/2)*((449)-1)/2) = 1, by norm_num,

have h52: 449-1 = 7*64, by norm_num,
have h53: 7 ∣ 7*64, from dvd_mul_right 7 64,
have h54: 7 ∣ (449-1), from eq.subst h52 h53,
have h55: (7:ℤ) ∣ (449-1), sorry,
have h56: 1 ≡ 449 [MOD 7], from nat.modeq.modeq_of_dvd h55,
have h57: 449 ≡ 1 [MOD 7], from nat.modeq.symm h56,
have h58: legendre_sym 449 prime_7 = legendre_sym 1 prime_7, from legendre_sym_refl 449 1 prime_7 h57,
have h59: 1-1^2=7*0, by norm_num,
have h60: 7 ∣ 7*0, from dvd_mul_right 7 0,
have h61: 7 ∣ 1-1^2, from eq.subst h59 h60,
have h62: (7:ℤ) ∣ 1-1^2, sorry,
have h63: 1 ≡ 1^2 [MOD 7], from nat.modeq.modeq_of_dvd h62,

have : quadratic_res 1 7, 
begin 
unfold quadratic_res,
existsi 1,
exact h63,
end,

have h64: legendre_sym 1 prime_7 = 1,
begin
unfold legendre_sym,
split_ifs,
refl,
exfalso,
apply h_1,
split,
exact this,
exact dec_trivial,
end,

have j27: (legendre_sym 7 H1)*(legendre_sym 449 prime_7) = 1, from eq.trans h50 h51,
have j28: (legendre_sym 7 H1)*(legendre_sym 1 prime_7) = 1, from eq.subst h58 j27,
have j29: (legendre_sym 7 H1)*1 = 1, sorry,
--have j30: 1*(legendre_sym 7 H1) = legendre_sym 7 H1, from one_mul (legendre_sym 7 H1),
--have j31: (legendre_sym 7 H1)*1 = 1*(legendre_sym 7 H1), from mul_comm (legendre_sym 7 H1) 1,  
have j32: (legendre_sym 7 H1)*1 = (legendre_sym 7 H1), from mul_one (legendre_sym 7 H1),
have j33: (legendre_sym 7 H1) = (legendre_sym 7 H1)*1, from eq.symm j32,
have a4: legendre_sym 7 H1 = 1, from eq.trans j33 j29,


exact calc 
 legendre_sym 210 H1 = (legendre_sym 2 H1)*(legendre_sym 105 H1) : by rw eq.trans h3 h4
            ... = (legendre_sym 2 H1)*(legendre_sym (3*35) H1) : by rw h7 
            ... = (legendre_sym 2 H1)*((legendre_sym 3 H1)*(legendre_sym 35 H1)) : by rw legendre_sym_mul 3 35 H1
            ... = (legendre_sym 2 H1)*(legendre_sym 3 H1)*(legendre_sym 35 H1) : by rw mul_assoc 
            ... = (legendre_sym 2 H1)*(legendre_sym 3 H1)*(legendre_sym (5*7) H1) : by rw h11
            ... = (legendre_sym 2 H1)*(legendre_sym 3 H1)*((legendre_sym 5 H1)*(legendre_sym 7 H1)) : by rw h12
            ... = (legendre_sym 2 H1)*(legendre_sym 3 H1)*(legendre_sym 5 H1)*(legendre_sym 7 H1) : by rw ←mul_assoc
            ... = 1*(legendre_sym 3 H1)*(legendre_sym 5 H1)*(legendre_sym 7 H1) : by rw a1
            ... = 1*(-1)*(legendre_sym 5 H1)*(legendre_sym 7 H1) : by rw a2
            ... = 1*(-1)*1*(legendre_sym 7 H1) : by rw a3
            ... = 1*(-1)*1*1 : by rw a4
            ... = -1 : by norm_num,



sorry,

--have (legendre_sym 2 H1)*(legendre_sym 105 H1), from legendre_sym_mul 2 105 H1,
end

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