import algebra.group
import chris_hughes_various.zmod
import group_theory.order_of_element

instance (n : nat) : pos_nat (nat.succ n) := ⟨nat.succ_pos _⟩ 
instance : decidable_eq (units (zmod 5)) := 
λ x y, decidable_of_iff _ ⟨ units.ext, λ _,by simp *⟩

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
    have h5 : (A.val).val * a_1.val % n = 1 % n, simp [h3],
    {

        sorry,
    },
    have h6 : (A.val).val * a_1.val ≡ 1 [MOD n], by rwa nat.modeq,
    have h4 :  ↑n ∣ ↑((A.val).val * a_1.val) - ↑1, from nat.modeq.dvd_of_modeq h6.symm,
    rw nat.gcd_comm,
    rw nat.gcd_rec,
    
    suffices : nat.coprime ((A.val).val % n) n, exact this,

    --rw ←h3,
    have h7 : ∃ (c : ℤ), ↑((A.val).val * a_1.val) - ↑1 = ↑n * c, from exists_eq_mul_right_of_dvd h4,
    apply exists.elim h7,
    intros,
    --rw nat.modeq.modeq_iff_dvd at h3,
    --have h4 : 

    sorry,
},
{
    sorry
} 
end,
inv_val := begin 

sorry 
end},
left_inv := begin 

sorry end,
right_inv := begin sorry end,
}

#print nat.gcd
#check exists_eq_mul_right_of_dvd
#check int.coe_nat_eq

--instance fintype_units_zmodn (n : ℕ) : fintype {a // 0 ≤ a ∧ a < n ∧ nat.gcd a n = 1} := sorry

instance (n : ℕ) [pos_nat n]: fintype (units (zmod n)) := fintype.of_equiv _ (equiv.symm (coprime_zmodn_units n))

#print notation ≃

-- #eval @order_of (units (zmod 5)) _ _ _ ⟨(2 : zmod 5), 2⁻¹, rfl, rfl⟩