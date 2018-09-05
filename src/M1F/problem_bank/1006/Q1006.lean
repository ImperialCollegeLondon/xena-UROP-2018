import data.fintype
open fintype
/- 6. Say A and B are finite sets, with sizes a and b respectively. Prove that the set B^A of functions A → B has size b^a. What about the case a = b = 0?
-/
variables {A B : Type} [fintype A] [fintype B]
