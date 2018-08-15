import data.nat.prime data.nat.gcd data.nat.modeq data.nat.gcd algebra.group chris_hughes_various.zmod group_theory.order_of_element M3P14.order_zmodn_kmb M3P14.phi

open zmod nat

/- Gives actual number when evaluating (e.g. #5 becomes 5) -/
instance (n : ℕ) : has_repr (zmod n) := ⟨repr ∘ fin.val⟩ 
--instance  {α : Type*} [monoid α] [has_repr α] : has_repr (units α) := ⟨repr ∘ units.val⟩ 

-- Thanks Chris
lemma order_of_dvd_of_pow_eq_one {d n : ℕ} [pos_nat n]  (a : units (zmod n)) (h : a ^ d = 1) : order_of a ∣ d :=
by_contradiction
(λ h₁, nat.find_min _ (show d % order_of a < order_of a,
from nat.mod_lt _ (nat.pos_of_ne_zero (order_of_ne_zero _)))
⟨mt nat.dvd_of_mod_eq_zero h₁, by rwa ← pow_eq_mod_order_of⟩)

--set_option pp.all true
/- define a function that given a n nats and coprime, gives back (a : units (zmod n)) -/  
def units_zmod_mk (a n : ℕ ) (h : nat.coprime a n) [pos_nat n] : units (zmod n) := 
{
    val := a,
    inv := a⁻¹,
    val_inv := by rw [mul_inv_eq_gcd n a, coprime.gcd_eq_one h];dsimp;rw zero_add,
    inv_val := by rw [mul_comm, mul_inv_eq_gcd n a, coprime.gcd_eq_one h];dsimp;rw zero_add,
}

def order_of_zmod (a n : ℕ) [pos_nat n] : ℕ := if h : nat.coprime a n then @order_of (units (zmod n)) _ _ _ (units_zmod_mk a n h) else 0

theorem not_coprime_pow_mod (a d n : ℕ) (h1 : a ^ d ≡ 1 [MOD n]) (h2 : ¬coprime a n) : d = 0 := sorry

-- is that true?
theorem zmod_card_pow (a n d : ℕ) (h : coprime a n) [pos_nat n] : a^fintype.card (units (zmod n)) ≡ 1 [MOD n] := sorry

@[simp] lemma units.coe_pow {α : Type*} [monoid α] (u : units α) (n : ℕ) : (↑(u ^ n) : α) = u ^ n :=
by induction n; simp [*, _root_.pow_succ]

-- can we prove it without h?
--set_option pp.implicit true
--set_option pp.notation false
theorem order_zmod_div (a n d : ℕ) (h : coprime a n) [pos_nat n] : a^d ≡ 1 [MOD n] → order_of_zmod a n ∣ d := 
begin
    intro h2,
    unfold order_of_zmod,
    cases (classical.em (nat.coprime a n)),
    {
        rw dif_pos h,
        rw eq_iff_modeq_nat.symm at h2,
        
        have pow : (units_zmod_mk a n h) ^ d  = 1,
        { apply units.ext,
          suffices : (↑(units_zmod_mk a n h ^ d) : zmod n) = 1,
            simp [this],
          have h2' : (↑(a ^ d) : zmod n) = 1,
            rw h2,
            simp,
          clear h2,
          rw ←h2',
          suffices : (↑(units_zmod_mk a n h) : zmod n) = a,
            simp [this],
          refl,
        },
        exact order_of_dvd_of_pow_eq_one (units_zmod_mk a n h) pow,
    },
    exact absurd h h_1,
end

#print units
--lemma to prove phi and fincard are the same


#eval fintype.card (units (zmod 15))

#eval fintype.card (units (zmod 12))
#eval order_of_zmod 7 12
#eval 7^2 % 12

#eval order_of_zmod 4 9
#eval 4^3 % 9

#check prime.dvd_iff_not_coprime
#check modeq.dvd_of_modeq
#check order_of_dvd_card_univ
#check fintype.card
#check fintype.elems (units (zmod 10))
#check dvd_trans
#check (units_zmod_mk 5 7) 

theorem order_zmod_div_phi_n (a n : ℕ) (h : coprime a n) [pos_nat n] : order_of_zmod a n ∣ phi n :=
begin
    have : a ^ (phi n) ≡ 1 [MOD n], from euler_phi_thm a n h,
    exact order_zmod_div a n (phi n) h this,
end

theorem pow_order_units_zmod_eq_one (a n : ℕ) [pos_nat n] (h : coprime a n) : (units_zmod_mk a n h) ^ order_of (units_zmod_mk a n h) = 1 :=
pow_order_of_eq_one (units_zmod_mk a n h)



theorem pow_order_zmod_eq_one (a n : ℕ) [pos_nat n] : (a : zmod n) ^ order_of_zmod a n = (1 : zmod n) :=
begin
    have em : nat.coprime a n ∨ ¬ nat.coprime a n, from (classical.em (nat.coprime a n)),
    unfold order_of_zmod,
    cases em,
    have one_eq : (1 : zmod n) = (1 : units (zmod n)), by simp,
    rw [dif_pos em,units_zmod_mk, one_eq,←(pow_order_units_zmod_eq_one a n em)],
    show ↑(units_zmod_mk a n em) ^ order_of (units_zmod_mk a n em) = ↑(units_zmod_mk a n em ^ order_of (units_zmod_mk a n em)),
    simp,
    rw dif_neg em,
    refl,
end



def primitive_root (a n : ℕ) [pos_nat n] := coprime a n ∧ order_of_zmod a n = phi n

theorem primitive_root_existence (n : ℕ) [pos_nat n] : ∃ a : ℕ, (primitive_root a n) ↔ n = 1 ∨ n = 2 ∨ n = 4 ∨ ∃ p r : ℕ, prime p ∧ r > 0 → (n = p^r ∨ n = 2*p^r) := sorry

