import algebra.group
import chris_hughes_various.zmod
import group_theory.order_of_element

instance (n : nat) : pos_nat (nat.succ n) := ⟨nat.succ_pos _⟩ 
instance : decidable_eq (units (zmod 5)) := 
λ x y, decidable_of_iff _ ⟨ units.ext, λ _,by simp *⟩

lemma gcd_one_of_unit (n : ℕ) [pos_nat n] (u : units (zmod n)) :
nat.gcd (u.val.val) n = 1 :=
begin
  let abar := u.val, let bbar := u.inv, --  in zmod n
  let a := abar.val, let b := bbar.val, -- in z
  have H : (a * b) % n = 1 % n,
    show (abar.val * bbar.val) % n = 1 % n,
    rw ←mul_val,
    rw u.val_inv,
    refl,
  let d := nat.gcd a n,
  show d = 1,
  rw ←nat.dvd_one,
  rw ←dvd_mod_iff (gcd_dvd_right a n),
  rw ←H,
  rw dvd_mod_iff (gcd_dvd_right a n),
  apply dvd_mul_of_dvd_left,
  exact gcd_dvd_left a n
end

/-
set_option pp.notation false
set_option pp.implicit true
-/
def coprime_zmodn_units (n : ℕ) [pos_nat n] : equiv (units (zmod n)) {a : zmod n // ∃ b, a * b = 1} :=
{ to_fun := λ u, ⟨u.1 , u.2, u.3⟩,
inv_fun := λ A, {val := (A.val.val), inv := ((A.val.val)⁻¹),
val_inv :=  
begin 

cases (classical.em (n > 1)),
{
    have eq : ∃ (b : zmod n), A.val * b = 1, from A.2,
    apply exists.elim eq,
    intros a_1 a_2,
    
    rw zmod.mul_inv_eq_gcd n (A.val.val),
    --rw gcd_one_of_unit,
    
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

    have dvd_sub : nat.gcd n ((A.val).val) ∣ (((A.val).val) * a_1.val) - (n * int.nat_abs a), from nat.dvd_sub uneq h7' h12,
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
    have n_1 : n = 1, from nat.le_antisymm (le_of_not_gt h) (nat.succ_le_of_lt _inst_1.pos),
    show (((A.val).val) : zmod n) * ((((A.val).val)) : zmod n)⁻¹ = 1,
    
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

-- noncomputable def units_equiv_coprime {n : ℕ} [pos_nat n] : 
-- units (zmod n) ≃ {a : zmod n // ∃ b, a * b = 1} :=
-- { to_fun := λ a, ⟨a, a.2, a.3⟩,
-- inv_fun := λ a, ⟨a.1, (a⁻¹).1, 
-- by rw mul_comm; exact classical.some_spec a.2⟩,
-- left_inv := λ a, units.ext (by cases a; refl),
-- right_inv := λ ⟨_, _⟩, rfl }

--try to prove
lemma mul_inv_eq_gcd (n : ℕ) (a : zmod n) [pos_nat n]: (a * a⁻¹).val = nat.gcd (a.val) n := 
begin 
    sorry
end


--instance fintype_units_zmodn (n : ℕ) : fintype {a // 0 ≤ a ∧ a < n ∧ nat.gcd a n = 1} := sorry

instance (n : ℕ) [pos_nat n]: fintype (units (zmod n)) := fintype.of_equiv _ (equiv.symm (coprime_zmodn_units n))
#eval @order_of (units (zmod 5)) _ _ _ ⟨(2 : zmod 5), 2⁻¹, rfl, rfl⟩

#print notation ≃