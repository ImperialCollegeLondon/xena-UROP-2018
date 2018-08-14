import data.real.basic 
import chris_hughes_various.exponential.exponential

definition is_deriv (f : ℝ → ℝ) (x : ℝ) (d : ℝ) : Prop :=
-- d = derivative of f at x
-- limit of f(x+h)-f(x) / h = d as h tends to zero 
∀ ε > 0, ∃ δ > 0, ∀ h, abs h < δ ∧ h ≠ 0 → abs ((f (x + h) - f x) / h - d) < ε  
--#print group

definition is_differentiable_at (f : ℝ → ℝ) (x : ℝ) : Prop :=
∃ d, is_deriv f x d

definition is_differentiable_on (f : ℝ → ℝ) (X : set ℝ) : Prop :=
∀ x ∈ X, is_differentiable_at f x

definition is_differentiable (f : ℝ → ℝ) : Prop :=
∀ x, is_differentiable_at f x

theorem deriv_is_unique (f : ℝ → ℝ) (x : ℝ) (d e : ℝ) :
is_deriv f x d → is_deriv f x e → d = e := sorry

theorem deriv_is_linear1 (f : ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ) (d e : ℝ) :
is_deriv f x d → is_deriv g x e → is_deriv (λ t, f t + g t) x (d + e) := sorry 

theorem deriv_is_linear2 (f : ℝ → ℝ) (x : ℝ) (d : ℝ) (μ : ℝ) :
is_deriv f x d → is_deriv (λ t, μ * f t) x (μ * d) := sorry 

-- sorry Patrick
theorem product_rule (f g : ℝ → ℝ) (x : ℝ) (d e : ℝ) :
is_deriv f x d → is_deriv g x e → is_deriv (λ t, f t * g t) x (d * g x + f x * e) := sorry

theorem chain_rule (f g : ℝ → ℝ) (x : ℝ) (d e : ℝ) :
is_deriv f x d → is_deriv g (f x) e → is_deriv (g ∘ f) x (e * d) := sorry

theorem exp_deriv (x : ℝ) : is_deriv (λ t : ℝ, (exp t).re) x (exp x).re := sorry
 