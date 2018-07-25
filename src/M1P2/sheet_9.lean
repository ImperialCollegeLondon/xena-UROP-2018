import algebra.euclidean_domain data.set data.complex.basic data.int.modeq

variables {R : Type*} [euclidean_domain R]
variables a b : ℤ

def gaussian_ints : ℂ := ⟨a,b⟩ 
--def gaussian_ints_val :  → ℕ := a^2 + b^2
--def valuation : 
def poly_coeff_rat := list rat -- could also use finsupp

def ints_adj_sqrt (n : ℤ) := set.range (λ x : ℤ × ℤ, x.1 + x.2 * nat.sqrt n.nat_abs)

-- 1. Let d ∈ Z be such that ℤ ∌ √d ,and let x,y ∈ Z[√d]. Verify the identity N(xy) = N(x)N(y), where N(r+s√d)=r^2−ds^2.
theorem sheet09_q1 (d : ℤ) : (d ≡ 2 [ZMOD 4] ∨ d ≡ 3 [ZMOD 4])  := sorry
-- 2. Let R be a ring with unity, and let u be a unit in R. Show that u√n us a unit for any n ∈ Z. Hence or otherwise, show that the the ring Z[√2] has infinitely many units.
--theorem sheet09_q2 
-- 3∗. Suppose R is a finite integral domain. Prove that R is a field. Look carefully at your proof. To what extent does your proof make full use of the hypotheses? Formulate and prove a more general result about finite commutative rings with unity.
--theorem sheet09_q3
-- 4. Which of the following elements are irreducible in the rings specified?

-- (a) 2 ∈ ℤ[i]. 

-- (b) 1+2√2 ∈ ℤ[√2]. 

-- (c) 1+2√−2 ∈ ℤ[√−2]. 

-- (d) 5 ∈ ℤ[i].

-- (e) 7 ∈ ℤ[i].

-- (f) x^2+3x+1 ∈ ℚ[x].

-- (g) x^2−x−6 ∈ ℚ[x]. 

-- (h) x^4+x^2+1 ∈ ℚ[x].

-- (i) x^3+3x+2 ∈ ℤ_7[x].

-- 5. Factorize the following ring elements into irreducibles.

-- (a) 3 + 5i ∈  ℤ[i]. 
    --e.g 1+i,4+i

-- (b) 4+2√−2 ∈  ℤ[√−2]
    -- 

-- (c) x^6−1 ∈ ℝ[x].

-- 6. Use the Euclidean algorithm to find the highest common factor for each of the following pairs.

-- (a) 3+√3 and 12 ∈ ℤ[√3]. 

-- (b) 7+i and 5+3i ∈ ℤ[i].

-- (c) x^6 and x^8+x^7+1 ∈ ℂ[x]. 

-- (d) x^3+x+1 and x5+1 ∈ ℝ[x].