class Euclidean_plane (point : Type) :=
-- Equidistance of 4 Points
(eqd : point → point → point → point → Prop)
-- between A B C means B is on the line segment AC
(B : point → point → point → Prop)

(reflex : ∀ a b : point, eqd a b b a)
(trans : ∀ a b p q r s, eqd a b p q → eqd a b r s → eqd p q r s)
(id_eqd : ∀ a b c, eqd a b c c → a = b)
(segment_construction : ∀ a b c q, ∃ x, B q a x → eqd a x b c)
(five_segment : ∀ a b c d a' b' c' d', a ≠ b → B a b c → B a' b' c' → eqd a b a' b' 
→ eqd b c b' c' → eqd a d a' d' → eqd b d b' d' → eqd c d c' d')
(betweenness : ∀ a b, B a b a → a = b)
(inner_pasch : ∀ a b c p q, B a p c → B b q c → ∃ x, B p x b → B q x a)
(two_dimensions : ∃ a b c, ¬B a b c → ¬B b c a → ¬B c a b)
(not_three_dimensions : ∀ a b c p₁ p₂, p₁ ≠ p₂ → eqd a p₁ a p₂ → eqd b p₁ b p₂ 
→ eqd c p₁ c p₂ → (B a b c ∨ B b c a ∨ B c a b))
(euclids : ∀ a b c d t, B a d t → B b d c → a ≠ d → ∃ x y, B a b x → B a c y → B y t x)
(continuity : ∀ X Y : set point, 
  (∃ a, ∀ x y, x ∈ X → y ∈ Y → B a x y) → (∃ b, ∀ x y, x ∈ X → y ∈ Y → B x b y))
(reflexivity_betweenness : ∀ a b, B a b b)
(between_itself : ∀ a b, a = b → B a b a)
(inner_trans : ∀ a b c d, B a b d → B b c d → B a b c)
(outer_trans : ∀ a b c d, B a b c → B b c d → b ≠ c → B a b d)
(inner_connectivity : ∀ a b c d, B a b d → B a c d → (B a b c ∨ B a c b))
(outer_connectivity : ∀ a b c d, B a b c → B a b d → a ≠ b → (B a c d ∨ B a d c))
(equal_distances : ∀ a b c, a = b → eqd a c b c)
(unique_triangle : ∀ a b c d c' d' x, eqd a c a c' → eqd b c b c' → B a d b → B a d' b 
→ B c d x → B c' d' x → d ≠ x → d' ≠ x → c = c')
(existence_triangle : ∀ a b a' b' c' p, eqd a b a' b' → ∃ c x, eqd a c a' c' → eqd b c b' c' 
→ B c x p → (B a b x ∨ B b x a ∨ B x a b))
(density_betweenness : ∀ x z, x ≠ z → ∃ y, x ≠ y → z ≠ y → B x y z)
(adding_distances : ∀ x y z x' y' z', B x y z → B x' y' z' → eqd x y x' y' 
→ eqd y z y' z' → eqd x z x' z')
(subtracting_distances : ∀ x y z x' y' z', B x y z → B x' y' z' → eqd x z x' z' 
→ eqd y z y' z' → eqd x y x' y')

open Euclidean_plane 

variables {point : Type} [Euclidean_plane point]

example (a b : point) : eqd a a b b :=
    sorry