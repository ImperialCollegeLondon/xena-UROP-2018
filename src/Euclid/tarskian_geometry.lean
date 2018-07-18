import euclid.axioms
open Euclidean_plane 

variables {point : Type} [Euclidean_plane point]

theorem refl_eqd (a b : point) : eqd a b a b :=
eqd_trans b a a b a b (eqd_refl b a) (eqd_refl b a)

theorem symm_eqd (a b c d : point) : eqd a b c d → eqd c d a b :=
assume h : eqd a b c d,
eqd_trans a b c d a b h (dist_reflex a b)

theorem trans_eqd (a b c d e f: point) : eqd a b c d → eqd c d e f → eqd a b e f :=
assume h h1,
eqd_trans c d a b e f (dist_symm a b c d h) h1

theorem twopoint4 (a b c d : point) : eqd a b c d → eqd b a c d := sorry

theorem twopoint5 (a b c d : point) : eqd a b c d → eqd a b d c := sorry

-- a "setoid" is just a silly computer science name for a type with an equiv reln
instance point_setoid : setoid (point × point) :=
{ r := λ ⟨a,b⟩ ⟨c,d⟩, eqd a b c d,
  iseqv := ⟨λ ⟨a,b⟩, refl_eqd a b,λ ⟨a,b⟩ ⟨c,d⟩, symm_eqd a b c d,λ ⟨a,b⟩ ⟨c,d⟩ ⟨e,f⟩, trans_eqd a b c d e f⟩
}

-- this type denotes the equiv classes. You may never need it but it's
-- a good test to see if you've got the definitions right!
definition distance_values (point : Type) [Euclidean_plane point] := 
quotient (@point_setoid point _)