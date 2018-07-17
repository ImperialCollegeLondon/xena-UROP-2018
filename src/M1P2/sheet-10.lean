import algebra.ring algebra.group_power data.nat.prime data.nat.basic data.int.modeq algebra.group_power group_theory.subgroup algebra.group data.set.basic data.nat.gcd init.algebra.ring data.complex.basic data.finsupp data.nat.sqrt algebra.euclidean_domain
open nat 
--1. For each of the following rings R, and elements a and b, find d = hcf(a,b), and calculate s, t ∈ R such that as + bt = d.
variables {R : Type*} [ring R]
variables a b : ℤ

--def d : ℤ := gcd a b

def gaussian_ints : ℂ := ⟨a,b⟩ 

def poly_coeff_rat := list rat -- could also use finsupp

def ints_adj_sqrt (n : ℤ) := 
set.range (λ x : ℤ × ℤ, x.1 + x.2 * nat.sqrt n.nat_abs)

--(a) a=4+3i,b=2−4i ∈ Z[i].
--theorem sheet10_q1_a (x y : gaussian_ints) (ha : a = ⟨4,3⟩) (ha : b = ⟨2,-4⟩)

--(b) a(x)=x^4−2x^2−x+4,b(x)=x^3+2x^2+x−1 ∈ Q[x].
--theorem sheet10_q1_b (x y : poly_coeff_rat) (ha x = [4,1,-2,0,1]) (hb y = [-1,1,2,1]) : 

--(c) a(x)=x^5−x^2−x−1,b(x)=x^4+2x^2+x+1 ∈ Q[x].
--theorem sheet10_q1_c (x y : poly_coeff_rat) (ha x = [-1,-1,-1,0,0,1]) (hb y = [1,1,2,0,1]) : 

--2. Find an irreducible element of ℤ[√3] that is not prime
    -- e.g : 2 + √3 i think works

--3. Show that R = ℤ[√3] is a Euclidean domain with Euclidean function If a=1+3 3,b=3−4 3inZ[√3],find d=hcf(a,b), and calculate δ(a) = |N(a)|, where N is the norm map.s, t ∈ R such that as + bt = d.
def R' := ints_adj_sqrt 3
-- def euc_func () := 


--theorem sheet10_q3 

--4. Let ω=e^2πi/3 ∈ C, and let Z[ω] be the set {x + yω | x, y ∈ Z} ⊆ C. 

--(a) Show that Z[ω] is a ring under the usual operations + and · on C. 

--(b) Define N:Z[ω]→Z by N(x+yω)=(x+yω)(x+yω)=x^2 +y^2 −xy. show that N(a)N(b) = N(ab) for all a,b ∈ Z[ω]. 

--(c) Find the units of Z[ω].

-- 5. (a) Show that the only integer solution to the equation y^3 = 4x^2 − 1 is x = 0 and y = −1. 
theorem sheet10_q5_a (x y : ℤ) : y^3 = 4*x^2 - 1 → x = 0 ∧ y = -1 := sorry 
--(b) Find all integer solutions to y3 = x2 + 1.
theorem sheet10_q5_b (x y : ℤ) : y^3 = x^2 + 1 → x = 0 ∧ y = 1 := sorry 
-- 6. Let p be a prime number congruent to 3 mod 4. Let a,b ∈ Z. Show that if p divides a2 + b2, then p divides both a and b. [Hint: use Fermat’s Little Theorem.]
theorem sheet10_q6 (a b : ℤ) (p : ℕ) (hp : prime p) (hq: p ≡ 3 [MOD 4]) : ↑p ∣ (a^2 + b^2) → ↑p ∣ a ∧ ↑p ∣ b := sorry 
--7. Show that y^3 = x^2 − 7 has no integer solutions. [Hint: Write this as y^3 +8 = x^2 + 1, show that the left-hand side must have a prime divisor congruent to 3 mod 4, and then use Qu. 6.]
theorem sheet10_q7 (x y : ℤ) : y^3 = x^2 - 7 → false := sorry -- need to add "has no solns"