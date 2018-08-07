import algebra.group
import chris_hughes_various.zmod
import group_theory.order_of_element

instance (n : nat) : pos_nat (nat.succ n) := ⟨nat.succ_pos _⟩ 
instance : decidable_eq (units (zmod 5)) := 
λ x y, decidable_of_iff _ ⟨ units.ext, λ _,by simp *⟩

/-
set_option pp.notation false
set_option pp.implicit true
-/
theorem coprime_zmodn_units (n : ℕ) [pos_nat n] : equiv (units (zmod n)) {a : zmod n // ∃ b, a * b = 1} :=
{ to_fun := λ u, ⟨u.1 , u.2, u.3⟩,
inv_fun := λ A, {val := (A.val).val, inv := ((A.val).val⁻¹),
val_inv :=  begin 
cases (classical.em (n > 1)),
{
    have eq : ∃ (b : zmod n), A.val * b = 1, from A.2,
    apply exists.elim eq,
    intros a_1 a_2,
    rw zmod.mul_inv_eq_gcd n (A.val.val),
    have h3 : (A.val * a_1).val = (1 : zmod n).val , simp [a_2],
    rw zmod.mul_val at h3,
    have h5 : (A.val).val * a_1.val % n = 1 % n, simp [h3], refl,
    have h6 : (A.val).val * a_1.val ≡ 1 [MOD n], by rwa nat.modeq,
    have h4 :  ↑n ∣ ↑((A.val).val * a_1.val) - ↑1, from nat.modeq.dvd_of_modeq h6.symm,
    rw nat.gcd_comm,
    have h7 : nat.gcd n ((A.val).val) ∣ ((A.val).val), from nat.gcd_dvd_right _ _, 
    have h7' : nat.gcd n ((A.val).val) ∣ ((A.val).val) * a_1.val, from dvd_mul_of_dvd_left h7 a_1.val,    
    have h8 : ∃ (c : ℤ), ↑((A.val).val * a_1.val) - ↑1 = ↑n * c, from exists_eq_mul_right_of_dvd h4,
    apply exists.elim h8,
    intros,
    have h9 : (nat.gcd n ((A.val).val) : ℤ) ∣ n , from int.coe_nat_dvd.mpr (nat.gcd_dvd_left _ _),
    have h10 : (nat.gcd n ((A.val).val) : ℤ) ∣ n * a, from dvd_mul_of_dvd_left h9 a, 
    have h11 : (nat.gcd n ((A.val).val) : ℤ) ∣ n * (int.nat_abs a : ℤ), 
    refine dvd_trans h10 (mul_dvd_mul_left _ (int.dvd_nat_abs.2 (dvd_refl _))),
    have h12 : nat.gcd n ((A.val).val) ∣ n * int.nat_abs a, from int.coe_nat_dvd.mp h11,
    have uneq : ((A.val).val * a_1.val) ≥ n * int.nat_abs a,
    {
        sorry
    },

    have dvd_sub : nat.gcd n ((A.val).val) ∣ (((A.val).val) * a_1.val) - (n * int.nat_abs a), from nat.dvd_sub uneq h7' h12 ,
    have eq_1 : (((A.val).val) * a_1.val) - (n * int.nat_abs a) = 1,
    {
        sorry
    },
    have gcd_dvd_1 : nat.gcd n ((A.val).val) ∣ 1, by rwa eq_1 at dvd_sub,
    have gcd_eq_1 : nat.gcd n ((A.val).val) = 1, from nat.dvd_one.mp gcd_dvd_1,
    rw gcd_eq_1,
    simp,
},
{
    sorry
} 
end,
inv_val := begin 
sorry, 
end},
left_inv := begin 

sorry end,
right_inv := begin sorry end,
}

#check nat.dvd_sub
#check exists_eq_mul_right_of_dvd
#check int.coe_nat_eq
#check nat.coprime.coprime_dvd_left
#check int.coe_nat_dvd
#check eq.subst 
#check nat.dvd_one

--instance fintype_units_zmodn (n : ℕ) : fintype {a // 0 ≤ a ∧ a < n ∧ nat.gcd a n = 1} := sorry

instance (n : ℕ) [pos_nat n]: fintype (units (zmod n)) := fintype.of_equiv _ (equiv.symm (coprime_zmodn_units n))

#print notation ≃

-- #eval @order_of (units (zmod 5)) _ _ _ ⟨(2 : zmod 5), 2⁻¹, rfl, rfl⟩