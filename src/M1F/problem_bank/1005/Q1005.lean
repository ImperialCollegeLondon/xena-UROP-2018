import data.real.basic algebra.group_power
/- 5∗. This relatively straightforward (if you’ve understood the idea correctly) question makes sure that you understand the composition of functions, and how it differs from other things like multiplication of functions.
Say f and g are functions from ℝ to ℝ defined by f(x) = x^2 + 3 and g(x) = 2x. Write down explicit formulae for the following functions:
-/ 
--variables {f g : ℝ → ℝ}
variable {x : ℝ}
def f : ℝ → ℝ := λ x, x^2 + 3 
def g : ℝ → ℝ := λ x, 2*x

--(i) f ◦ g
def h1 : ℝ → ℝ := g ∘ f 
theorem Q1005i : h1 x = 2*x^2 + 6 := sorry
--(ii) g ◦ f
def h2 : ℝ → ℝ := g ∘ f 
theorem Q1005ii : h2 x = 4*x^2 + 3 := sorry
--(iii) x 􏰀→ f(x)g(x) 
--def h3 : ℝ → ℝ := λ f g, f * g  
--(iv) x 􏰀→ f(x) + g(x)
--def h4 : ℝ → ℝ := λ f g, f + g  
--(v) x 􏰀→ f(g(x))
--def h5 : ℝ → ℝ := f (g x)