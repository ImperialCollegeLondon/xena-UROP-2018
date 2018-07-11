structure Euclidean_plane :=

(point : Type)
-- Equidistance of 4 Points
(eqd : point → point → point → point → Prop)
-- between A B C means B is on the line segment AC
(B : point → point → point → Prop)
(reflex : ∀ a b : point, eqd a b b a)
(trans : ∀ a b p q r s, eqd a b p q → eqd p q r s → eqd a b r s)
(id_eqd : ∀ a b c, eqd a b c c → a = b)
(segment_construction : ∀ a b c q, ∃ x, B q a x → eqd a x b c)
(five_segment : ∀ a b c d a' b' c' d', a ≠ b → B a b c → B a' b' c' → eqd a b a' b' → eqd b c b' c' 
→ eqd a d a' d' → eqd b d b' d' → eqd c d c' d')
(betweenness : ∀ a b, B a b a → a = b)
(inner_pasch : ∀ a b c p q, B a p c → B b q c → ∃ x, B p x b → B q x a)
--something

(continuity : ∀ X Y : set point, 
  (∃ a, ∀ x y, x ∈ X → y ∈ Y → B a x y) → (∃ b, ∀ x y, x ∈ X → y ∈ Y → B x b y)
)

