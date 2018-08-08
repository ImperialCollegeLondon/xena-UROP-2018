import analysis.metric_space algebra.module inner_product_spaces.basic
import inner_product_spaces.norm_space

universes u v
variables V W : Type

section norm_space

-- Banach space is a complete normed space.
class banach_space (V : Type) extends norm_space V: Type :=
(complete: complete_space ℝ)

noncomputable instance banach_to_metric_space : has_coe (banach_space V) (metric_space V) :=
⟨λh, by 
    { have h1 := h.to_norm_space,  
    cases (@to_metric_space _ h1) with h2, 
    exact h2 h1 } ⟩

end norm_space
-- theorem completion 