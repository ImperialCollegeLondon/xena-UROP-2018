import Euclid.axioms
open Euclidean_plane
variables {point : Type} [Euclidean_plane point]

theorem prop1 (a b : point) : ∃ c, eqd a b a c → eqd a b b c := sorry
theorem prop2 (a b c : point) : ∃ d, eqd a d b c := sorry
theorem prop3 (a b c d : point) (h : ¬eqd a b c d) : (∃ x, B a x b → eqd a x c d) ∨ (∃ x, B c x d → eqd a b c x) := sorry
--theorem prop4
--theorem prop5
--theorem prop6
theorem prop7 (a b c d c' d' x : point) : eqd a c a c' → eqd b c b c' → B a d b → B a d' b 
→ B c d x → B c' d' x → d ≠ x → d' ≠ x → c = c' := unique_tri a b c d c' d' x
--theorem prop8
--theorem prop9
theorem prop10 (a b : point) : ∃ c, B a c b → eqd a c b c := sorry
--theorem prop11
--theorem prop12
--theorem prop13
--theorem prop14
--theorem prop15
--theorem prop16
--theorem prop17
--theorem prop18
--theorem prop19
--theorem prop20
--theorem prop21
--theorem prop22
--theorem prop23
--theorem prop24
--theorem prop25
--theorem prop26
--theorem prop27
--theorem prop28
--theorem prop29
theorem prop30 (a b c d e f : point) {h1 : a ≠ b} {h2 : c ≠ d} {h3 : e ≠ f} : parallel a b c d h1 h2 → parallel a b e f h1 h3 → parallel c d e f h2 h3:=
sorry


