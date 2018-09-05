import data.real.basic  algebra.group_power

open function
--2. For each of the following functions, decide whether or not they are injective, surjective, bijective. Proofs required!
variable RH : Prop
-- need to say that RH is undecidable 

--(i) f : R → R, f(x) = 1/x if x ̸= 0 and f(0) = 0.
noncomputable def f : ℝ → ℝ := λ x, 1/x
theorem Q1002i (x : ℝ) (f : ℝ → ℝ) : bijective f := sorry
--(ii) f : Z → Z, f(n) = 2*n + 1.
def f1 : ℤ → ℤ := λ n, 2*n + 1
theorem Q1002ii (n : ℤ) (f1 : ℤ → ℤ) : bijective f1 := sorry
--(iii) f : R → R, f(x) = x^3. [you can assume that every positive real has a unique positive real cube root, even though you haven’t really seen a formal proof of this yet.]
def f2 : ℝ → ℝ := λ x, x^3
theorem Q1002iii (x : ℝ) (f2 : ℝ → ℝ) : bijective f2 := sorry
--(iv) f : R → R defined by f(x) = x^3 if the Riemann hypothesis is true, and f(x) = −x if not. [NB the is a hard unsolved problem in mathematics; nobody currently knows if it is true or false.]
def f3 : ℝ → ℝ := if RH = tt then λ x, x^3 else λ x, -x
theorem Q1002iv (x : ℤ) (f4 : ℤ → ℤ) : bijective f3 := sorry
--(v) (hard) f : Z → Z, f(n) = n^3 − 2*n^2 + 2*n − 1
def f4 : ℤ → ℤ := λ n, n^3 - 2*n^2 + 2*n - 1
theorem Q1002v (x : ℤ) (f4 : ℤ → ℤ) : bijective f4 := sorry