import linear_algebra.basic algebra.field data.vector2 data.complex.basic

open vector_space field set complex
universes u v w
variables (V : Type u)

variables [field α] [vector_space α β] {a b : α} {x : β}

#print notation • 

class has_inner_product [vector_space ℂ] extends vector_space ℂ β 
