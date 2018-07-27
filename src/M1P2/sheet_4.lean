import algebra.group_power data.complex.basic group_theory.coset

universes u v w x
variables {G : Type u} {G₂ : Type v} {G₃ : Type w} {G₄ : Type x}
variables [group G] [comm_group G₂] [add_group G₃] [add_comm_group G₄]

-- sheet 4

-- 4. Let S be the two-element set {a, b}. Show that there are precisely 16 distinct binary operations on S. How many of them make S a group? Find a formula for the total number of binary operations on a set of n elements.
--def S' := {}
--theorem sheet04_q4:

-- 5. Prove that multiplication of ℂ numbers is associative.

theorem sheet04_q05 (z z₁ z₂ : ℂ) : z * z₁ * z₂ = z * (z₁ * z₂) := by apply mul_assoc z z₁ z₂


-- 6. Which of the following are groups? Prove one, delete another.
--(a)
--theorem sheet04_q6a_is_T:
--theorem sheet04_q6a_is_F:

-- Let S be the set of all real numbers except −1. For a, b ∈ S define a ∗ b = ab + a + b. Show that (S, ∗) is a group. 
def s := {x : ℝ | x ≠ -1}

def op (m n : s) [has_add s] [has_mul s] : s := ⟨m * n + m + n, sorry⟩ -- want to prove that this operation is from s to s to s rather than s to s to ℝ 

local notation m ~ n := op m n 

--def Is_group {G:Type} (g:set G) (op: g → g → g): Prop := (∀ (x y z ∈ g), op (op x y) z = op x (op y z)) ∧ 
--(∃ i ∈ g , (∀x ∈ g,op x i = x ∧ op i x = x) ∧ (∀ x ∈ g, ∃ xin:G, op x xin =i ∧ op xin x =i))

--theorem q7: Is_group s ~ := sorry 

--theorem q7 (a b : set s) 

-- 8. Let G be a group, and let a, b, c ∈ G. Prove the following facts.
--(a) If ab=ac then b=c.
theorem sheet04_q8a (a b c : G) : a * b = a * c ↔ b = c := by apply mul_left_inj a

--(b) The equation axb = c has a unique solution for x ∈ G.
theorem sheet04_q8b (a b c : G) : ∃! x : G, a * x * b = c := 
begin
intros,
existsi (a⁻¹ * c * b⁻¹),simp [mul_assoc],
assume y h,
rw ← h,
simp [mul_assoc],
end
--(c) (a^{−1})^{−1} = a.
theorem sheet04_q8c (a : G) : a⁻¹⁻¹ = a := by apply inv_inv a
--(d) (ab)^{−1} = b^{-1}a^{−1}.
theorem sheet04_q8d (a b : G) : (a*b)⁻¹ = b⁻¹*a⁻¹ := by apply mul_inv_rev a b
-- 9. Let G be a group, and let e be the identity of G. Suppose that x∗x=e for all x∈G. Show that y ∗ z = z ∗ y for all y, z ∈ G.
theorem sheet04_q9 (y z : G) (hp : ∀x : G, x*x = 1) : y * z = z * y := sorry
