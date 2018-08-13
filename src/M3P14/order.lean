import data.nat.prime data.nat.gcd data.nat.modeq data.nat.gcd algebra.group chris_hughes_various.zmod group_theory.order_of_element M3P14.order_zmodn_kmb M3P14.phi

open zmod nat
instance (n : nat) : pos_nat (nat.succ n) := ⟨nat.succ_pos _⟩ 
instance (n : ℕ) [pos_nat n] : fintype (units (zmod n)) := fintype.of_equiv _ (equiv.symm (coprime_zmodn_units n))
instance decidable_eq_units_zmod (n : ℕ) [pos_nat n] : decidable_eq (units (zmod n)) :=  λ x y, decidable_of_iff _ ⟨ units.ext, λ _,by simp *⟩
 
#eval @order_of (units (zmod 7)) _ _ _ ⟨(2 : zmod 7), 2⁻¹, rfl, rfl⟩
#eval @order_of (units (zmod 5)) _ _ _ ⟨(2 : zmod 5), 2⁻¹, rfl, rfl⟩
#eval @order_of (units (zmod 7)) _ _ _ ⟨(1 : zmod 7), 1⁻¹, rfl, rfl⟩

def order_of_zmod (a n : ℕ) [pos_nat n] : ℕ := @order_of (units (zmod n)) _ _ _ ⟨a, a⁻¹, sorry, sorry⟩ 

#eval order_of_zmod 7 53

theorem order_zmod_div (a n d : ℕ) (h : coprime a n) [pos_nat n] : a^d ≡ 1 [MOD n] → order_of_zmod a n ∣ d := sorry

theorem order_zmod_div_phi_n (a n : ℕ) (h : coprime a n) [pos_nat n] : order_of_zmod a n ∣ phi n :=
begin
have : a ^ (phi n) ≡ 1 [MOD n], from euler_phi_thm a n h,
exact order_zmod_div a n (phi n) h this,
end

@[simp] lemma units.coe_pow {α : Type*} [monoid α] (u : units α) (n : ℕ) : (↑(u ^ n) : α) = u ^ n :=
by induction n; simp [*, _root_.pow_succ]

#print units.one_coe

theorem pow_order_zmod_eq_one (a n : ℕ) (h: coprime a n) [pos_nat n] : (a : zmod n) ^ (order_of_zmod a n) = (1 : zmod n) := sorry
--by rw [units.coe_inj, ← units.coe_pow, pow_order_of_eq_one]

def primitive_root (a n : ℕ) [pos_nat n] := coprime a n ∧ order_of_zmod a n = phi n

theorem primitive_root_existence (n : ℕ) [pos_nat n] : ∃ a : ℕ, (primitive_root a n) ↔ n = 1 ∨ n = 2 ∨ n = 4 ∨ ∃ p r : ℕ, prime p ∧ r > 0 → (n = p^r ∨ n = 2*p^r) := sorry