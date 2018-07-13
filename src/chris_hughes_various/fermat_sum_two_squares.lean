import data.int.basic data.fintype data.nat.modeq data.set.finite data.nat.prime tactic.ring
universe u

local attribute [instance, priority 0] classical.prop_decidable

local attribute [instance] set_fintype

open fintype finset

noncomputable lemma fintype_of_injective {α β : Type*} {f : α → β} [fintype β]
  (hf : function.injective f) : fintype α :=
if h : nonempty α 
then have i : inhabited α := classical.inhabited_of_nonempty h,
  of_surjective (@function.inv_fun _ i _ f) $ @function.inv_fun_surjective _ i _ _ hf
else ⟨∅, λ x, h ⟨x⟩⟩

lemma bijective_of_involution {α : Type*} {f : α → α} (hf : ∀ x, f (f x) = x) : function.bijective f := 
⟨λ x y hxy, by rw [← hf x, ← hf y, hxy], λ x, ⟨f x, hf x⟩⟩

lemma int.coe_nat_nonneg (n : ℕ) : (0 : ℤ) ≤ n := int.coe_nat_le_coe_nat_of_le $ nat.zero_le n

lemma finset_even_card_of_involution {α : Type*} {f : α → α} (s : finset α) : (∀ x ∈ s, f x ≠ x)
    → (∀ x ∈ s, f (f x) = x) → (∀ x : α, x ∈ s → f x ∈ s) → 2 ∣ card s := 
finset.strong_induction_on s $ λ s ht hf₁ hf₂ hs, or.by_cases (decidable.em (s = ∅)) (by simp {contextual := tt}) $
λ h, let ⟨x, hx⟩ := exists_mem_of_ne_empty h in
let t := filter (λ y, y ≠ x ∧ y ≠ f x) s in
have hts : t ⊂ s := ⟨filter_subset _, λ h, by have := subset_iff.1 h hx; simp * at *⟩,
have ht₂ : ∀ y, y ∈ t → f y ∈ t := λ y hyt,
  have hys : y ∈ s := mem_of_subset hts.1 hyt,
  have h₁ : f y ≠ x := λ h₂,
    have h₃ : y = f x := by rw [← h₂, hf₂ _ hys],
    by rw h₃ at hyt; simp * at *,
  have h₂ : f y ≠ f x := λ h₂,
    have hxy : y = x := by rw [← hf₂ _ hys, ← hf₂ _ hx, h₂],
    by simpa [hxy] using hyt,
  by simp * at *,
have hst : s = insert (f x) (insert x t) := 
  ext.2 $ λ z, ⟨λ h, by simp [*, or_iff_not_and_not] at * {contextual := tt}, 
  λ h, by rw [mem_insert, mem_insert] at h; exact or.by_cases h (λ h, h.symm ▸ hs _ hx)
  (λ h, or.by_cases h (λ h, h.symm ▸ hx) (λ h, mem_of_subset hts.1 h))⟩,
have hxt : x ∉ t := by simp [t],
have hfxt : f x ∉ insert x t := by simp [t, hf₁ x hx],
have hft₁ : ∀ y ∈ t, f y ≠ y := λ y hyt, hf₁ y (mem_of_subset hts.1 hyt),
have hft₂ : ∀ y ∈ t, f (f y) = y := λ y hyt, hf₂ y (mem_of_subset hts.1 hyt),
by rw [hst, card_insert_of_not_mem hfxt, card_insert_of_not_mem hxt, add_assoc];
  exact (nat.dvd_add_iff_right (ht _ hts hft₁ hft₂ ht₂)).1 dec_trivial

lemma fintype_even_card_of_involution {α : Type*} {f : α → α} [fintype α] (hf₁ : ∀ x : α, f x ≠ x) 
    (hf₂ : ∀ x : α, f (f x) = x) : 2 ∣ card α :=
finset_even_card_of_involution _ (λ x hx, hf₁ x) (λ x hx, hf₂ x) (λ x hx, mem_univ _)

lemma set.card_univ {α : Type*} [fintype α] : fintype.card (set.univ : set α) = fintype.card α :=
card_congr ⟨λ a, a.1, λ a, ⟨a, set.mem_univ _⟩, λ ⟨_, _⟩, rfl, λ _, rfl⟩

lemma odd_card_of_involution_of_unique_fixed_point {α : Type*} {f : α → α} [fintype α]
    (hf₂ : ∀ x : α, f (f x) = x) (hf₃ : ∃! a : α, f a = a) : card α % 2 = 1 :=
let ⟨a, (ha₁ : f a = a), ha₂⟩ := hf₃ in
let f' : {b : α // b ≠ a} → {b : α // b ≠ a} :=
λ x, ⟨f x, λ h, x.2 ((bijective_of_involution hf₂).1 (h.trans ha₁.symm))⟩ in
have hf'₁ : ∀ x, f' x ≠ x := λ ⟨x, hx⟩ hx', 
  have hx₂ : f x = x := subtype.mk.inj hx',
  hx (ha₂ x hx₂), 
have hf'₂ : ∀ x, f' (f' x) = x := λ ⟨x, hx⟩, subtype.eq (hf₂ x),
have hab : a ∉ {b : α | b ≠ a} := by simp,
have hα : fintype.card α = fintype.card {b : α | b ≠ a} + 1 := 
  by rw [← set.card_fintype_insert' _ hab, ← set.card_univ];
  congr;
  exact set.ext (λ x, by simp [classical.em]),
let ⟨c, (hc : card {b : α | b ≠ a} = c * 2)⟩ := exists_eq_mul_left_of_dvd 
    (fintype_even_card_of_involution hf'₁ hf'₂) in
by rw [hα, hc, add_comm]; exact nat.add_mul_mod_self_right _ _ _

lemma exists_fixed_point_of_involution_of_odd_card {α : Type*} {f : α → α} [fintype α]
    (ha : card α % 2 = 1) (hf₂ : ∀ x : α, f (f x) = x) : ∃ x, f x = x :=
by_contradiction $ λ hf₁, (dec_trivial : 0 ≠ 1) $ (nat.mod_eq_zero_of_dvd 
(fintype_even_card_of_involution (forall_not_of_not_exists hf₁) hf₂)).symm.trans ha

open nat

private def S (p : ℕ) : set (ℤ × ℤ × ℤ) := {v | ((v.1) * (v.1) + 4 * v.2.1 * v.2.2 = ↑p) 
    ∧ 0 ≤ v.1 ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2}

lemma nat.prime_not_square (n : ℕ) : ¬prime (n * n) := 
λ h, or.by_cases (h.2 _ $ dvd_mul_right n n) 
(λ h₁, (dec_trivial : ¬ 1 ≥ 2) (h₁ ▸ h : prime (1 * 1)).1) $
λ h₁, have h₂ : n * 1 = n * n := by rwa mul_one,
have h₃ : 1 = n := (@nat.mul_left_inj n 1 n (prime.pos (h₁.symm ▸ h))).1 h₂,
(dec_trivial : ¬ 1 ≥ 2) (h₃.symm ▸ h : prime (1 * 1)).1

@[reducible] private def f₁ : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := λ ⟨x, y, z⟩, (x, z, y)

@[reducible] private def f₂ : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := 
λ ⟨x, y, z⟩, if x + z < y 
  then (x + 2 * z, z, y - x - z) 
  else (if 2 * y < x 
      then (x - 2 * y, x - y + z, y)
      else (2 * y - x, y, x - y + z))

variables {p : ℕ} (hp : prime p) (hp₁ : p % 4 = 1)
include hp hp₁

private lemma x_pos : ∀ v : ℤ × ℤ × ℤ, v ∈ S p → (0 : ℤ) < v.1 := 
λ ⟨x, y, z⟩ ⟨hv, hx, hy, hz⟩,
lt_of_le_of_ne hx $ λ (h : 0 = x), have hp₂ : 4 * y * z = p := by simp [h.symm, hv.symm],
absurd (show (4 : ℤ) ∣ -1, from add_sub_cancel' (4 * (y * z)) (-1 : ℤ) ▸ 
dvd_sub (mul_assoc 4 y z ▸ hp₂.symm ▸ modeq.dvd_of_modeq hp₁.symm) (dvd_mul_right _ _)) dec_trivial

private lemma yz_pos : ∀ v : ℤ × ℤ × ℤ, v ∈ S p → (0 : ℤ) < v.2.1 ∧ (0 : ℤ) < v.2.2 :=
λ ⟨x, y, z⟩ ⟨hv, hx, hy, hz⟩,
have hxx : ↑p ≠ x * x := @int.nat_abs_mul_self x ▸ (λ h, nat.prime_not_square (int.nat_abs x) 
  (by rwa ← int.coe_nat_inj h)),
⟨lt_of_le_of_ne hy $ λ (h : 0 = y), hxx $ eq.symm (by simpa [h.symm] using hv), 
lt_of_le_of_ne hz $ λ (h : 0 = z), hxx $ eq.symm (by simpa [h.symm] using hv)⟩

private lemma v_lt_p_add_one : ∀ v : ℤ × ℤ × ℤ, v ∈ S p → int.nat_abs v.1 < p + 1 ∧ 
    int.nat_abs v.2.1 < p + 1 ∧ int.nat_abs v.2.2 < p + 1 :=
λ ⟨x, y, z⟩ ⟨(hv : x * x + 4 * y * z = p), (hx : 0 ≤ x), (hy : 0 ≤ y), (hz : 0 ≤ z)⟩,
begin
  suffices : (int.nat_abs x : ℤ) ≤ p ∧ (int.nat_abs y : ℤ) ≤ p ∧ (int.nat_abs z : ℤ) ≤ p,
    repeat {rw int.coe_nat_le at this},
    exact ⟨lt_succ_of_le this.1, lt_succ_of_le this.2.1, lt_succ_of_le this.2.2⟩,
  have hyz := yz_pos hp hp₁ (x, y, z) ⟨hv, hx, hy, hz⟩,
  rw [← int.nat_abs_mul_self, ← int.nat_abs_of_nonneg hy, ← int.nat_abs_of_nonneg hz] at hv,
  rw ← hv,
  exact ⟨le_add_of_le_of_nonneg (int.coe_nat_le.2 $ le_mul_self _)
      (mul_nonneg (mul_nonneg dec_trivial (int.coe_nat_nonneg _)) (int.coe_nat_nonneg _)), 
    le_add_of_nonneg_of_le (int.coe_nat_nonneg _) (by rw mul_right_comm; 
      exact le_mul_of_ge_one_left' (int.coe_nat_nonneg _) (@int.add_one_le_of_lt 0 _ $
      mul_pos (dec_trivial : (4 : ℤ) > 0) $ by rw int.nat_abs_of_nonneg hz; exact hyz.2)), 
    le_add_of_nonneg_of_le (int.coe_nat_nonneg _) 
      (le_mul_of_ge_one_left' (int.coe_nat_nonneg _) (@int.add_one_le_of_lt 0 _
      (mul_pos (dec_trivial : (4 : ℤ) > 0) (by rw int.nat_abs_of_nonneg hy; exact hyz.1))))⟩
end

private noncomputable lemma fintype_S : fintype (S p) :=
fintype_of_injective $ show function.injective (λ v, ⟨⟨int.nat_abs v.1.1, 
(v_lt_p_add_one hp hp₁ v.1 v.2).1⟩, ⟨int.nat_abs v.1.2.1, (v_lt_p_add_one hp hp₁ v.1 v.2).2.1⟩,
⟨int.nat_abs v.1.2.2, (v_lt_p_add_one hp hp₁ v.1 v.2).2.2⟩⟩ : 
S p → fin (p+1) × fin (p+1) × fin (p+1)), from λ ⟨⟨a₁, a₂, a₃⟩, ⟨ha, ha₁, ha₂, ha₃⟩⟩ 
⟨⟨b₁, b₂, b₃⟩, ⟨hb, hb₁, hb₂, hb₃⟩⟩ h,
have h : int.nat_abs a₁ = int.nat_abs b₁ ∧ int.nat_abs a₂ = int.nat_abs b₂ 
  ∧ int.nat_abs a₃ = int.nat_abs b₃ := by simpa [subtype.mk.inj_eq, 
    iff.intro fin.veq_of_eq fin.eq_of_veq] using h,
subtype.eq $ by
  repeat {rw [← int.coe_nat_eq_coe_nat_iff, int.nat_abs_of_nonneg, int.nat_abs_of_nonneg] at h};
  finish

private lemma f₁_S : ∀ v : ℤ × ℤ × ℤ, v ∈ S p → f₁ v ∈ S p :=
λ ⟨x, y, z⟩, by simp [S, mul_comm, *, mul_assoc, mul_left_comm, *, f₁] {contextual := tt}

private lemma f₁_invo_on_S : ∀ v : ℤ × ℤ × ℤ, f₁ (f₁ v) = v := λ ⟨x, y, z⟩, rfl

private lemma f₂_S : ∀ v : ℤ × ℤ × ℤ, v ∈ S p → f₂ v ∈ S p := 
λ ⟨x, y, z⟩ ⟨hv, hx, hy, hz⟩, or.by_cases (decidable.em (x + z < y))
(λ h, ⟨by simp [f₂, h, hv.symm, S, mul_add, add_mul]; ring,
by unfold f₂; rw if_pos h; exact add_nonneg hx (mul_nonneg dec_trivial hz),
by unfold f₂; rw if_pos h; exact hz, le_of_lt (by have h₂ := sub_pos.2 h; simpa [f₂, h] using h₂)⟩)
$ λ h, have h' : y ≤ x + z := le_of_not_gt h,
or.by_cases (decidable.em (2 * y < x)) (λ h₁, ⟨by simp [f₂, h, h₁, hv.symm, S, mul_add, add_mul]; ring,
le_of_lt (by have h₃ := sub_pos.2 h₁; simpa [f₂, h₃, h, h₁] using h₃),
by have h₃ := sub_nonneg.2 h'; simpa [f₂, h, h₁, h₃] using h₃, by simpa [f₂, h, h₁] using hy⟩) $
λ h₁, have h₁' : x ≤ 2 * y := le_of_not_gt h₁,
⟨by simp [f₂, h, h₁, hv.symm, S, mul_add, add_mul]; ring, 
by have h₃ := sub_nonneg.2 h₁'; simpa [f₂, h, h₁, h₃] using h₃,
by simpa [f₂, h, h₁] using hy, 
by have h₃ := sub_nonneg.2 h'; simpa [f₂, h, h₁] using h₃⟩

private lemma f₂_invo_on_S : ∀ v : ℤ × ℤ × ℤ, v ∈ S p → f₂ (f₂ v) = v := 
λ ⟨x, y, z⟩ hv,
have xp : 0 < x := x_pos hp hp₁ (x, y, z) hv,
have yzp : 0 < y ∧ 0 < z :=  yz_pos hp hp₁ (x, y, z) hv,
 or.by_cases (decidable.em (x + z < y)) (λ h,
have h₁ : ¬ x + (y + (2 * z + (-x + -z))) < z :=
  have h₁ : x + (y + (2 * z + (-x + -z))) = y + z := by ring,
  not_lt_of_ge (h₁.symm ▸ le_add_of_nonneg_left hv.2.2.1),
by simp[f₂, h, h₁, xp]; ring) $ 
λ h, or.by_cases (decidable.em (2 * y < x))
(λ h₁, have h₂ : y + -(2 * y) < z + -y :=
  have h₂ : y + -(2 * y) = -y := by ring, 
  h₂.symm ▸ lt_add_of_pos_left _ yzp.2,
by simp[f₂, h, h₁, h₂]; ring) $ 
λ h₁, have h₂ : ¬ x + (z + (2 * y + (-x + -y))) < y :=
  have h₁ : x + (z + (2 * y + (-x + -y))) = z + y := by ring,
  not_lt_of_ge (h₁.symm ▸ le_add_of_nonneg_left hv.2.2.2),
have h₃ : ¬ 0 < -x := not_lt_of_ge $ le_of_lt $ neg_neg_of_pos xp,
by simp [f₂, h, h₁, h₂, h₃]; ring

private lemma f₂_fixed_point : ∃! v : S p, f₂ v = v :=
have hp4 : (0 : ℤ) ≤ p / 4 := int.div_nonneg (int.coe_nat_nonneg _) dec_trivial,
have h : ¬ (1 : ℤ) + p / 4 < 1 := not_lt_of_ge $ le_add_of_nonneg_right hp4,
⟨⟨(1, 1, (p / 4 : ℤ)),
⟨show (1 : ℤ) + 4 * (p / 4) = p,
from have h : (p : ℤ) % 4 = 1 := (int.coe_nat_eq_coe_nat_iff _ _).2 hp₁,
have h₁ : (p : ℤ) = p % 4 + 4 * (p / 4) := (int.mod_add_div _ _).symm,
by rw [h₁] {occs := occurrences.pos [2]}; rw h,
dec_trivial, dec_trivial, hp4 ⟩⟩,
⟨by simp [f₂, h, (dec_trivial : ¬ (2 : ℤ) < 1)]; refl, 
λ ⟨⟨x, y, z⟩, ⟨hv, hx, hy, hz⟩ ⟩ hf,
have xp : 0 < x := x_pos hp hp₁ (x, y, z) ⟨hv, hx, hy, hz⟩,
have yzp : 0 < y ∧ 0 < z := yz_pos hp hp₁ (x, y, z) ⟨hv, hx, hy, hz⟩, 
or.by_cases (decidable.em (x + z < y))
(λ h₁, 
have h₂ : x + 2 * z ≠ x := λ h₃,
  have h₄ : x + 2 * z = x + 0 := by rwa add_zero,
  not_or dec_trivial (ne_of_lt yzp.2).symm (mul_eq_zero.1 ((add_left_inj _).1 h₄)),
by simpa [f₂, h₁, h₂] using hf) $ λ h₁, 
or.by_cases (decidable.em (2 * y < x))
(λ h₂, 
have h₃ : x + -(2 * y) ≠ x := λ h₄,
  have h₅ : x + -2 * y = x + 0 := by rwa [← neg_mul_eq_neg_mul, add_zero],
  not_or dec_trivial (ne_of_lt yzp.1).symm (mul_eq_zero.1 ((add_left_inj _).1 h₅)),
by simp [f₂, h₁, h₂, h₃] at hf; trivial) $ λ h₂, 
have hf₁ : 2 * y - x = x ∧ x + (z + -y) = z := by simp [f₂, h₁, h₂] at hf; assumption,
have hxy : y = x := by rw [sub_eq_iff_eq_add, ← two_mul] at hf₁;
  exact eq_of_mul_eq_mul_left dec_trivial hf₁.1,
subtype.eq $ show (x, y, z) = (1, 1, p / 4), from
begin 
  rw [hxy, mul_comm (4 : ℤ), mul_assoc] at hv,
  have hxp : int.nat_abs x ∣ p := int.coe_nat_dvd.1 (int.nat_abs_dvd.2 (hv ▸ dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _))),
  have h4 : ((4 : ℕ) : ℤ) = 4 := rfl,
  cases hp.2 _ (hxp) with h₃ h₃,
  { have h₄ : x = 1 := by rwa [← int.coe_nat_eq_coe_nat_iff, int.nat_abs_of_nonneg hx] at h₃,
    rw [← mod_add_div p 4, hp₁, h₄, int.coe_nat_add, int.coe_nat_one, mul_one, one_mul, add_left_cancel_iff,
        int.coe_nat_mul] at hv,
    have : z = p / 4 := eq_of_mul_eq_mul_left_of_ne_zero dec_trivial hv,
    rw [hxy, h₄, this] },
  { have h4 : ((4 : ℕ) : ℤ) = 4 := rfl,
    rw [← int.nat_abs_of_nonneg hx, ← int.nat_abs_of_nonneg hz, h₃, ← mul_add] at hv,
    have := int.eq_one_of_mul_eq_self_right (int.coe_nat_ne_zero.2 (ne_of_lt (prime.pos hp)).symm) hv,
    rw [← h4, ← int.coe_nat_mul, ← int.coe_nat_add, ← int.coe_nat_one, int.coe_nat_eq_coe_nat_iff] at this,
    have : p ≤ 1 := this ▸ (le_add_right p (4 * int.nat_abs z)),
    exact absurd (prime.gt_one hp) (not_lt_of_ge this) }
end ⟩ ⟩

theorem fermat_sum_two_squares : ∃ a b : ℕ, a^2 + b^2 = p := 
have fS : fintype (S p) := fintype_S hp hp₁,
let f₁' : S p → S p := λ ⟨v, hv⟩, ⟨f₁ v, f₁_S hp hp₁ _ hv⟩ in
let f₂' : S p → S p := λ ⟨v, hv⟩, ⟨f₂ v, f₂_S hp hp₁ _ hv⟩ in
have hf₁ : ∀ v, f₁' (f₁' v) = v := λ ⟨v, hv⟩, subtype.eq $ f₁_invo_on_S hp hp₁ v,
have hf₂ : ∀ v, f₂' (f₂' v) = v := λ ⟨v, hv⟩, subtype.eq $ f₂_invo_on_S hp hp₁ v hv,
have hf₂u : ∃! v : S p, f₂' v = v := 
  let ⟨⟨v, vS⟩, ⟨hv₁, hv₂⟩⟩ := f₂_fixed_point hp hp₁ in 
  ⟨⟨v, vS⟩, ⟨subtype.eq hv₁, λ ⟨w, wS⟩ hw, hv₂ ⟨w, wS⟩ (subtype.mk.inj hw) ⟩ ⟩,
let h := @odd_card_of_involution_of_unique_fixed_point _ _ fS hf₂ hf₂u in
let ⟨⟨⟨x, y, z⟩, hvp, ⟨hx, hy, hz⟩⟩, h⟩ := @exists_fixed_point_of_involution_of_odd_card _ _ fS h hf₁ in
have h : y = z := (prod.eq_iff_fst_eq_snd_eq.1 (prod.eq_iff_fst_eq_snd_eq.1 (subtype.mk.inj h)).2).2,
⟨int.nat_abs x, 2 * int.nat_abs y,
begin 
  simp only [nat.pow_succ, nat.pow_zero, one_mul],
  rw [mul_right_comm 2, mul_assoc, mul_assoc, ← int.coe_nat_eq_coe_nat_iff, int.coe_nat_add,
      int.nat_abs_mul_self, int.coe_nat_mul, int.coe_nat_mul, int.nat_abs_mul_self, ← hvp, h],
  simp,
  ring,
end⟩