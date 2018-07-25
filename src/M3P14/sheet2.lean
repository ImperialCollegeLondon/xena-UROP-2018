import data.nat.prime
import data.nat.modeq data.int.modeq
import analysis.real
import tactic.norm_num


open nat 

definition quadratic_res (a n: ℕ) := ∃ x: ℕ, a ≡ x^2 [MOD n]

local attribute [instance] classical.prop_decidable
noncomputable definition legendre_sym (a: ℕ) (p:ℕ): ℤ := 
if quadratic_res a p ∧ ¬ p ∣ a then 1 else 
if ¬ quadratic_res a p then -1 
else 0

theorem law_of_quadratic_reciprocity (p q : ℕ) : (legendre_sym p q)*(legendre_sym q p)=(-1)^(((p-1)/2)*((q-1)/2)) := sorry 

theorem legendre_sym_mul (a b p: ℕ) : legendre_sym (a*b) p = (legendre_sym a p)*(legendre_sym b p) := sorry

theorem legendre_sym_refl (a b p: ℕ) :  (a≡ b [MOD p] → legendre_sym a p = legendre_sym b p) :=sorry

theorem legendre_sym_supplementary_laws (p: ℕ): legendre_sym 2 p = (-1:ℤ)^((p^2-1)/8) := sorry 


-- Questions:
-- Compute 210/449 and 605/617 using quadratic reciprocity.
-- (449 and 617 are both prime).
-- TODO: how to prove it using quadratic reciprocity?
theorem q1 : ((legendre_sym 210 449) = (-1: ℤ)) ∧ ((legendre_sym 605 617) = (-1: ℤ) ) :=
begin
split,
have h1: 210 = 2*105, refl,
have h2: legendre_sym 210 449 = legendre_sym 210 449, refl, 
have h3: legendre_sym 210 449 = legendre_sym (2*105) 449, from eq.subst h1 h2, 
have h4: legendre_sym (2*105) 449 = (legendre_sym 2 449)*(legendre_sym 105 449), from legendre_sym_mul 2 105 449,
have h5: 105 = 3*35, refl,
have h6: legendre_sym 105 449 = legendre_sym 105 449, refl,
have h7: legendre_sym 105 449 = legendre_sym (3*35) 449, from eq.subst h5 h6, 
have h8: legendre_sym (3*35) 449 = (legendre_sym 3 449)*(legendre_sym 35 449), from legendre_sym_mul 3 35 449,
have h9: 35 = 5*7, refl,
have h10: legendre_sym 35 449 = legendre_sym 35 449, refl,
have h11: legendre_sym 35 449 = legendre_sym (5*7) 449, from eq.subst h9 h10,
have h12: legendre_sym (5*7) 449 = (legendre_sym 5 449)*(legendre_sym 7 449), from legendre_sym_mul 5 7 449,

have h:(-1: ℤ)^((449^2 -1)/8)= 1, by norm_num,

have h13: legendre_sym 2 449 = (-1:ℤ)^((449^2-1)/8), from legendre_sym_supplementary_laws 449, 
have a: legendre_sym 2 449 = 1, from eq.trans h13 h,  

have h14: (legendre_sym 3 449)*(legendre_sym 449 3) = (-1: ℤ)^(((3-1)/2)*((449-1)/2)), from law_of_quadratic_reciprocity 3 449,
have h15: (-1: ℤ)^(((3-1)/2)*((449-1)/2)) = 1, by norm_num,

have h16: 449-2 = 3*149, by norm_num,s
have h17: 3 ∣ 3*149, from dvd_mul_right 3 149,
have h18: 3 ∣ (449-2), from eq.subst h16 h17,
have h19: 449 ≡ 2 [MOD 3], from modeq_of_dvd h18,
--have h16: legendre_sym 449 3 = legendre_sym 2 3, from legendre_sym_refl 449 2 3,
calc 
 legendre_sym 210 449 = (legendre_sym 2 449)*(legendre_sym 105 449) : by rw eq.trans h3 h4
            ... = (legendre_sym 2 449)*(legendre_sym (3*35) 449) : by rw h7 
            ... = (legendre_sym 2 449)*((legendre_sym 3 449)*(legendre_sym 35 449)) : by rw legendre_sym_mul 3 35 449
            ... = (legendre_sym 2 449)*(legendre_sym 3 449)*(legendre_sym 35 449) : by mul_assoc 
            ... = (legendre_sym 2 449)*(legendre_sym 3 449)*(legendre_sym (5*7) 449) : by rw h11
            ... = (legendre_sym 2 449)*(legendre_sym 3 449)*((legendre_sym 5 449)*(legendre_sym 7 449)) : by rw h12
            ... = (legendre_sym 2 449)*(legendre_sym 3 449)*(legendre_sym 5 449)*(legendre_sym 7 449) : by rw ←mul_assoc
            ... = -1 : sorry, 



sorry,

--have (legendre_sym 2 449)*(legendre_sym 105 449), from legendre_sym_mul 2 105 449,
end 

#reduce 2* 655
 
-- Find all 6 primitive roots modulo 19.
--theorem q2a :

-- Show that if n is odd and a is a primitive root mod n, then a is aprimitive root mod 2n if a is odd, and a + n is a primitive root mod 2n if a is even. 
-- [HINT: Φ(2n) = Φ(n) when n is odd.]
--theorem q2b :

-- Let p be a prime and let a be a primitive root mod p. 
-- Show that a is also a primitive root mod p² if, and only if, a^p−1 is not congruent to 1 mod p².
-- [HINT: what is the order of a mod p? What does this say about the order of a mod p²?]
--theorem q3 :

-- Let p be a prime, and let a be an integer not divisible by p. 
-- Show that the equation x^d ≡ a (mod p) has a solution if, and only if, a^(p−1/(d,p−1)) ≡ 1 (mod p). 
-- Show further that if this is the case then this equation has (d, p − 1) solutions mod p.
-- [HINT: what happens when you fix a primitive root g mod p, and take the discrete log of the equation x^d ≡ a (mod p)?]
theorem q4 (p a x d: ℕ) (hp : prime p) : x^d ≡ a [MOD p] ↔ a^(p-1/(gcd d (p-1))) ≡ 1 [MOD p] := sorry

-- Let p be an odd prime different from 7. 
-- Show that 7 is a square mod p if, and only if, p is congruent to 1, 3, 9, 19, 25 or 27 modulo 28.
-- [HINT: use quadratic reciprocity to relate 7/p to p/7.]
theorem q5 (p x : ℕ) (hp: prime p) (hq: p ≠ 7) : x^2 ≡ 7 [MOD p] ↔ (p ≡ 1 [MOD 28] ∨ p ≡ 3 [MOD 28] ∨  p ≡ 9 [MOD 28] ∨ p ≡ 19 [MOD 28] ∨  p ≡ 25 [MOD 28] ∨ p ≡ 25 [MOD 28]) := sorry

-- Let n and m be relatively prime. Show that every element of (ℤ/nmℤ)^x has order dividing the least common multiple of Φ(n) and Φ(m).
--theorem q6a (n m : ℕ) (hp : gcd m n = 1): := sorry  

-- Show that if n and m are relatively prime, then ℤ/nmℤ has a primitive root if, and only if, both ℤ/nℤ and ℤ/mℤ have primitive roots, and (Φ(n), Φ(m)) = 1.
-- When can this happen?
--theorem q6b (n m : ℕ) (hp : gcd m n = 1) := sorry 

-- Suppose a is a primitive root modulo n. Show that a^d is also a primitive root modulo n for all d such that (d, Φ(n)) = 1.
-- [Hint: show that there exists k such that (a^d)^k is equal to a.]
--theorem q7 :

-- Show that if p is a prime congruent to ±1 mod 24 then none of 2, 3, 4, 6is a primitive root modulo p.
-- [Hint: show that 2 and 3 are squares mod p.]
theorem q8 (p : ℕ) (hp : prime p) : (p ≡ 1 [ZMOD 24] ∨ p ≡ -1 [ZMOD 24])  := sorry