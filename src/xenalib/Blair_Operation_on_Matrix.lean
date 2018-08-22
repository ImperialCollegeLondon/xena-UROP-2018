/-
Copyright (c) 2018 Keji Neri, Blair Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blair Shi


* `adj M` gives the adjugate matrix of M

-/

import .linear_map .ring_n_is_module_of_vector
import xenalib.Ellen_Arlt_matrix_rings
import xenalib.Keji_further_matrix_things

def minor {R : Type} [comm_ring R] {n : ℕ} (M : matrix R (n + 1) (n + 1)) (a b : ℕ):
matrix R n n :=
λ I J,
if (I.1 < a ∧ J.1 < b) 
then M I.1 J.1 
else 
  if (I.1 >= a ∧ J.1 < b)
  then M (I.1 + 1) J.1
  else
    if (I.1 >= a ∧ J.1 >= b)
    then M (I.1 + 1) (J.1 + 1)
    else M I.1 (J.1 + 1)

noncomputable def cofactor {R : Type} [comm_ring R] [comm_ring R] {n : ℕ} (M : matrix R (n + 1) (n + 1)) :
matrix R (n + 1) (n + 1) := λ I J, ((- 1) ^ (I.1 + J.1)) * (det (minor M I J))

noncomputable def adj {R : Type} [comm_ring R] {n : ℕ} (M : matrix R (n + 1) (n + 1)) :
matrix R (n + 1) (n + 1) := transpose (cofactor M)

