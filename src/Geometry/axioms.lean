class Euclidean_plane (point : Type) :=
-- Equidistance of 4 Points
(eqd : point → point → point → point → Prop)
-- Between A B C means B is on the line segment AC
(B : point → point → point → Prop)
[dec_B : ∀ a b c, decidable (B a b c)]
-- Existence of three points for two_dim
(P1 {} : point) (P2 {} : point) (P3 {} : point)

(eqd_refl : ∀ a b : point, eqd a b b a)
(eqd_trans : ∀ {a b p q r s}, eqd a b p q → eqd a b r s → eqd p q r s)
(id_eqd : ∀ {a b c}, eqd a b c c → a = b)
(seg_cons : ∀ a b c q, {x // B q a x ∧ eqd a x b c})
(five_seg : ∀ {a b c d a' b' c' d'}, a ≠ b → B a b c → B a' b' c' → eqd a b a' b' 
→ eqd b c b' c' → eqd a d a' d' → eqd b d b' d' → eqd c d c' d')
(bet_same : ∀ {a b}, B a b a → a = b)
(pasch : ∀ {a b c p q}, B a p c → B b q c → {x // B p x b ∧ B q x a})
(two_dim : ¬B P1 P2 P3 ∧ ¬B P2 P3 P1 ∧ ¬B P3 P1 P2)
(not_3dim : ∀ {a b c p q}, p ≠ q → eqd a p a q → eqd b p b q 
→ eqd c p c q → (B a b c ∨ B b c a ∨ B c a b))
(euclids : ∀ {a b c d t}, B a d t → B b d c → a ≠ d → { X : point × point  // B a b X.1 ∧ B a c X.2 ∧ B X.1 t X.2})
(cont : ∀ X Y : set point, 
  (∃ a, ∀ x y, x ∈ X → y ∈ Y → B a x y) → (∃ b, ∀ x y, x ∈ X → y ∈ Y → B x b y))