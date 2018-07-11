import Euclid.unordered_pairs

#check uprod 

structure Euclidean_plane :=
(point : Type)
-- distance between two points
(equidist : point → point → point → point → Prop)
-- between A B C means B is on the line segment AC
(between : point → point → point → Prop)
(reflex : ∀ a b : point, equidist a b b a)
(trans : ∀ a b p q r s, equidist a b p q → equidist p q r s → equidist a b r s)
(id_equidist : ∀ a b c, equidist a b c c → a = b)



open Euclidean_plane 
variable {EP : Euclidean_plane}

