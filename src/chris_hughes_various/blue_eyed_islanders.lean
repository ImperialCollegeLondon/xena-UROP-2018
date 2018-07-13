import data.nat.basic tactic.finish
open nat
def island_rules : ℕ → ℕ → ℕ → Prop
| 0        b B :=  (B = b ∨ B = b - 1) ∧ B > 0
| (succ d) b B := island_rules d b B ∧ 
                ((∀ c, island_rules d b c → c = b) ↔ (∀ c, island_rules d B c → c = B))

theorem init_island {d b B} : island_rules d b B → (B = b ∨ B = b - 1) ∧ B > 0 :=
nat.rec_on d id (λ d ih, ih ∘ and.left)

theorem blue_eyed_islander : ∀ d b, b > 0 → (d + 1 ≥ b ↔ ∀ B, island_rules d b B → B = b) := 
λ d, nat.rec_on d (λ b, nat.cases_on b (λ h, absurd h (dec_trivial : ¬0 > 0)) $ λ b, nat.cases_on 
b (λ h, ⟨λ h B hB, or.by_cases hB.left (λ h1, h1) (λ h1, false.elim $ (dec_trivial : ¬1 - 1 > 0) $
h1 ▸ hB.right), λ h, dec_trivial⟩) $ λ b h, ⟨λ h2, ((dec_trivial : ¬0 + 1 ≥ succ (succ
b)) h2).elim, λ hB, false.elim $ (succ_ne_self $ succ b).symm $ hB (succ b) ⟨or.inr (succ_sub_one $
succ b).symm, dec_trivial⟩⟩) $ λ d hi b hb, ⟨λ hd, or.by_cases (lt_or_eq_of_le hd) (λ h B hB, (hi
b hb).mp (le_of_succ_le_succ $ succ_le_of_lt h) B hB.left) $ λ h B hB, or.by_cases (init_island 
hB.left).left (λ h, h) $ λ h, hB.right.mpr ((hi B (init_island hB.left).right).mp $
le_of_succ_le_succ $ (((nat.sub_eq_iff_eq_add $ succ_le_of_lt hb).mp h.symm).trans $ add_one B) ▸
hd) B hB.left, λ hB, by_contradiction $ λ hd, Exists.rec_on (classical.not_forall.mp $ 
(iff_false_left $ not_le_of_gt $ lt_of_succ_lt $ lt_of_not_ge hd).mp $ hi b hb) $ λ B hB1, have
hB2 : island_rules d b B ∧ ¬B = b := (@not_imp _ _ $ classical.prop_decidable _).mp hB1, hB2.right
$ hB B ⟨hB2.left, iff.mpr (iff_false_left $ λ h, hB2.right $ h B hB2.left) $ (iff_false_left $
not_le_of_gt $ lt_of_succ_lt_succ (((nat.sub_eq_iff_eq_add $ succ_le_of_lt hb).mp (or.resolve_left
(init_island hB2.left).left hB2.right).symm) ▸ (lt_of_not_ge hd) : succ (d + 1) < B + 1)).mp $ hi
B (init_island hB2.left).right⟩⟩