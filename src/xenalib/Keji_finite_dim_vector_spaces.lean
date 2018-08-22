/- 
Copyright (c) 2018 Blair Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard, Blair Shi

This file is inspired by Johannes Hölzl's implementation of linear algebra in mathlib.

The thing we improved is this file describes finite dimentional vector spaces
-/

import algebra.module -- for definition of vector_space  
import linear_algebra.basic -- for definition of is_basis 
import data.list.basic
import analysis.real
universes u v 

class finite_dimensional_vector_space (k : Type u) (V : Type v) [field k] 
  extends vector_space k V :=
(ordered_basis : list V)
(is_ordered_basis : is_basis {v : V | v ∈ ordered_basis})


variables {k : Type u} {V : Type v}
variable [field k]
variable [module k V]
variables {a : k} {b : V}
variable [decidable_eq V]
include k 
#check list.has_union 
#check finset 
definition dimension (fvs : finite_dimensional_vector_space k V) : ℕ :=
fvs.ordered_basis.length
theorem Steinitz_exchange_lemma  (fvs : finite_dimensional_vector_space k V) {S T: list V}
 (SLD: linear_independent {v : V | v ∈ S}) (TSS: span{v : V | v ∈ T} = set.univ) : ∃ T': list V, 
 T' ⊆ T ∧  T'.length =T.length ∧ 
 span {v:V | v ∈ list.diff T  T' ∪ S} = (set.univ : set V) := 
  begin 
   
  end

 
