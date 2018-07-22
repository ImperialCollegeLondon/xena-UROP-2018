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
/-
(refl_bet : ∀ a b, B a b b)
(bet_itself : ∀ a b, a = b → B a b a)
(bet_symm : ∀ a b c , B a b c → B c b a)
(in_trans : ∀ a b c d, B a b d → B b c d → B a b c)
(out_trans : ∀ a b c d, B a b c → B b c d → b ≠ c → B a b d)
(in_conn : ∀ a b c d, B a b d → B a c d → (B a b c ∨ B a c b))
(out_conn : ∀ a b c d, B a b c → B a b d → a ≠ b → (B a c d ∨ B a d c))
(eq_dist : ∀ a b c, a = b → eqd a c b c)
(unique_tri : ∀ a b c d c' d' x, eqd a c a c' → eqd b c b c' → B a d b → B a d' b 
→ B c d x → B c' d' x → d ≠ x → d' ≠ x → c = c')
(existence_triangle : ∀ a b a' b' c' p, eqd a b a' b' → ∃ c x, eqd a c a' c' → eqd b c b' c' 
→ B c x p → (B a b x ∨ B b x a ∨ B x a b))
(dens_bet : ∀ x z, x ≠ z → ∃ y, x ≠ y → z ≠ y → B x y z)
(add_dist : ∀ x y z x' y' z', B x y z → B x' y' z' → eqd x y x' y' 
→ eqd y z y' z' → eqd x z x' z')
(sub_dist : ∀ x y z x' y' z', B x y z → B x' y' z' → eqd x z x' z' 
→ eqd y z y' z' → eqd x y x' y')
-/


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

/-
cont :
  ∀ {point : Type} [c : Euclidean_plane point] (X Y : set point),
    (∃ (a : point), ∀ (x y : point), x ∈ X → y ∈ Y → B a x y) →
    (∃ (b : point), ∀ (x y : point), x ∈ X → y ∈ Y → B x b y)


theorem intersect_circle (a b c q p r : point) : B c q p → B c p r → eqd c a c q → eqd c b c r 
→ ∃ x, B a x b ∧ eqd c x c p := begin
  intro Baqp,
  intro Bcpr,
  intro Ecacq,
  intro Ecbcr,
  let X := { x : point | B a x b ∧ ∃ x' : point, B c x' p ∧ eqd c x c x'},
  let Y := { y : point | B a y b ∧ ∃ y' : point, B p y' r ∧ eqd c y c y'},
  have H : ∃ a : point, ∀ x y, x ∈ X → y ∈ Y → B a x y,
    sorry,
  have H₂ := cont X Y H,
  cases H₂ with z Hz,
  existsi z,
  split,
  { apply Hz a b,
    { show B a a b ∧ ∃ (x' : point), B c x' p ∧ eqd c a c x',
      split,
        apply bet_symm,
        exact refl_bet _ _,
    existsi q,
      split,
        assumption,
        assumption
    },
    show B a b b ∧ ∃ (y' : point), B p y' r ∧ eqd c b c y',
    split,
      apply refl_bet,  
    existsi r,
    split,
      apply refl_bet,
      assumption
  },
  sorry 
  end 
-/

