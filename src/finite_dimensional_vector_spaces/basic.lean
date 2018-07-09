import algebra.module -- for definition of vector_space  
import linear_algebra.basic -- for definition of is_basis 
universes u v 

structure finite_dimensional_vector_space (k : Type u) (V : Type v) [field k] 
  extends vector_space k V :=
(ordered_basis : list V)
(is_ordered_basis : is_basis {v : V | v ∈ ordered_basis})
 

