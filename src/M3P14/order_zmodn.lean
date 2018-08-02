import algebra.group
import chris_hughes_various.zmod
import group_theory.order_of_element

instance (n : nat) : pos_nat (nat.succ n) := ⟨nat.succ_pos _⟩ 
instance : decidable_eq (units (zmod 5)) := 
λ x y, decidable_of_iff _ ⟨ units.ext, λ _,by simp *⟩

#check equiv
#check equiv (units (zmod 5)) nat

theorem coprime_zmodn_units (n : ℕ) [pos_nat n] : equiv (units (zmod n)) {a : zmod n // ∃ b, a * b = 1} :=
{ to_fun := λ u, ⟨u.1, u.2, u.3⟩,
inv_fun := λ a,{val := a,inv := begin sorry end,val_inv := begin sorry end,inv_val := begin sorry end},
left_inv := begin sorry end,
right_inv := begin sorry end,
}

--instance fintype_units_zmodn (n : ℕ) : fintype {a // 0 ≤ a ∧ a < n ∧ nat.gcd a n = 1} := sorry

instance (n : ℕ) [pos_nat n]: fintype (units (zmod n)) := fintype.of_equiv _ (equiv.symm (coprime_zmodn_units n))

#print notation ≃

-- #eval @order_of (units (zmod 5)) _ _ _ ⟨(2 : zmod 5), 2⁻¹, rfl, rfl⟩