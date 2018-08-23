import data.int.basic
import data.int.modeq
import data.int.order
import algebra.group_power
import tactic.ring
import chris_hughes_various.zmod
import M3P14.lqr

open nat 



lemma lemma_1_q_prime {q n x y a b : ℤ} (h_n : n > (0: ℤ)) (h_q : q = x^2 + n*y^2) (h_q_dvd : q ∣ (a^2 + n*b^2)) (h_ab : coprime (int.nat_abs a) (int.nat_abs b)) : 
prime_int q → (∃ c d : ℤ, (a^2+n*b^2)/q = c^2 + n*d^2 ∧ (coprime (int.nat_abs c) (int.nat_abs d))) := 
begin
intro,
have h1 : q ∣ x^2 * (a^2 + n*b^2), sorry,
sorry,
end

lemma lemma_1_q_4_n_3 {q n : ℤ} (h_n : n > (0: ℤ)) (h_q : ∃ x y : ℤ, q = x^2 + n*y^2) (h_q_dvd : ∃ a b : ℤ, q ∣ (a^2 + n*b^2)) (h_ab : coprime (int.nat_abs a) (int.nat_abs b)) : 
(q = 4 ∧ n = 3) → (∃ c d : ℤ, (a^2+n*b^2)/q = c^2 + n*d^2 ∧ (coprime (int.nat_abs c) (int.nat_abs d))) := 
begin
intro,
sorry,
end


lemma descent_step_1 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
∃ a b : ℤ, p ∣ (a^2 + b^2) ∧ (coprime (int.nat_abs a) (int.nat_abs b)) → (∃ x y : ℤ, p = x^2 + y^2) := sorry

lemma descent_step_2 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
∃ a b : ℤ, (p ∣ (a^2 + 2*b^2) ) ∧ (coprime (int.nat_abs a) (int.nat_abs b)) → ∃ x y : ℤ, p = x^2 + 2*y^2 := sorry

lemma descent_step_3 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
∃ a b : ℤ, (p ∣ (a^2 + 3*b^2) ) ∧ (coprime (int.nat_abs a) (int.nat_abs b)) → ∃ x y : ℤ, p = x^2 + 3*y^2 := sorry


lemma reciprocity_step_1 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) : 
p ≡ 1 [ZMOD 4] → ∃ a b : ℤ, (p ∣ (a^2 + b^2) ) ∧ (coprime (int.nat_abs a) (int.nat_abs b)) := sorry

lemma reciprocity_step_2 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) : 
((p ≡ 1 [ZMOD 8]) ∨ (p ≡ 3 [ZMOD 8])) → ∃ a b : ℤ, (p ∣ (a^2 + 2*b^2) ) ∧ (coprime (int.nat_abs a) (int.nat_abs b)) := sorry

lemma reciprocity_step_3 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) : 
((p = 1) ∨ (p ≡ 1 [ZMOD 3])) → ∃ a b : ℤ, (p ∣ (a^2 + 3*b^2) ) ∧ (coprime (int.nat_abs a) (int.nat_abs b)) := sorry


theorem Thm_1 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
∃ x y : ℤ, p = x^2 + y^2 ↔ p ≡ 1 [ZMOD 4] := sorry

theorem Thm_2 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
∃ x y : ℤ, p = x^2 + 2*y^2 ↔ ((p ≡ 1 [ZMOD 8]) ∨ (p ≡ 3 [ZMOD 8])) := sorry

theorem Thm_3 {p : ℤ} (hp : prime_int p ∧ int.nat_abs p ≠ 2) :
∃ x y : ℤ, p = x^2 + 3*y^2 ↔ ((p = 1) ∨ (p ≡ 1 [ZMOD 3])) := sorry


