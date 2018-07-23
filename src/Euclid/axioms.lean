class Euclidean_plane (point : Type) :=
-- Equidistance of 4 Points
(eqd : point → point → point → point → Prop)
-- Between A B C means B is on the line segment AC
(B : point → point → point → Prop)

(eqd_refl : ∀ a b : point, eqd a b b a)
(eqd_trans : ∀ a b p q r s, eqd a b p q → eqd a b r s → eqd p q r s)
(id_eqd : ∀ a b c, eqd a b c c → a = b)
(seg_cons : ∀ a b c q, ∃ x, B q a x ∧ eqd a x b c)
(five_seg : ∀ a b c d a' b' c' d', a ≠ b → B a b c → B a' b' c' → eqd a b a' b' 
→ eqd b c b' c' → eqd a d a' d' → eqd b d b' d' → eqd c d c' d')
(bet_same : ∀ a b, B a b a → a = b)
(pasch : ∀ a b c p q, B a p c → B b q c → ∃ x, B p x b ∧ B q x a)
(two_dim : ∃ a b c, ¬B a b c ∧ ¬B b c a ∧ ¬B c a b)
(not_3dim : ∀ a b c p q, p ≠ q → eqd a p a q → eqd b p b q 
→ eqd c p c q → (B a b c ∨ B b c a ∨ B c a b))
(euclids : ∀ a b c d t, B a d t → B b d c → a ≠ d → ∃ x y, B a b x ∧ B a c y ∧ B x t y)
(cont : ∀ X Y : set point, 
  (∃ a, ∀ x y, x ∈ X → y ∈ Y → B a x y) → (∃ b, ∀ x y, x ∈ X → y ∈ Y → B x b y))

open Euclidean_plane 

variables {point : Type} [Euclidean_plane point]
/-
theorem dist_reflex (a b : point) : eqd a b a b :=
eqd_trans b a a b a b (eqd_refl b a) (eqd_refl b a)

theorem dist_symm (a b c d : point) : eqd a b c d → eqd c d a b :=
assume h : eqd a b c d,
eqd_trans a b c d a b h (dist_reflex a b)

theorem dist_trans (a b c d e f: point) : eqd a b c d → eqd c d e f → eqd a b e f :=
assume h h1,
eqd_trans c d a b e f (dist_symm a b c d h) h1

-- a "setoid" is just a silly computer science name for a type with an equiv reln
instance point_setoid : setoid (point × point) :=
{ r := λ ⟨a,b⟩ ⟨c,d⟩, eqd a b c d,
  iseqv := ⟨λ ⟨a,b⟩,dist_reflex a b,λ ⟨a,b⟩ ⟨c,d⟩,dist_symm a b c d,λ ⟨a,b⟩ ⟨c,d⟩ ⟨e,f⟩,dist_trans a b c d e f⟩
}

-- this type denotes the equiv classes. You may never need it but it's
-- a good test to see if you've got the definitions right!
definition distance_values (point : Type) [Euclidean_plane point] := 
quotient (@point_setoid point _)
-/
--def parallel (a b c d : point) (h1 : a ≠ b) (h2 : c ≠ d) : Prop := ∀ x, col a b x → ((col a b c ∧ col a b d) ∨ ¬col c d x) 

--def circle (a b :point) : set point := {x : point | eqd a b a x}