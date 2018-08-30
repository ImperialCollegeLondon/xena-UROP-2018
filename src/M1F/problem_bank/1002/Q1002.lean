import data.real.basic 

open function
--2. For each of the following functions, decide whether or not they are injective, surjective, bijective. Proofs required!

--(i) f : R → R, f(x) = 1/x if x ̸= 0 and f(0) = 0.

--def f (ℝ → ℝ) : λ r, 1/r 
--theorem Q1002 (x : ℝ) (f : ℝ → ℝ) (hp: f $ x = 1/x) : bijective f := sorry
--(ii) f : Z → Z, f(n) = 2*n + 1.
--theorem Q1002ii (n : ℤ) (f : ℤ → ℤ) : bijective f := sorry
--(iii) f : R → R, f(x) = x^3. [you can assume that every positive real has a unique positive real cube root, even though you haven’t really seen a formal proof of this yet.]
--theorem Q1002 (x : ℝ) (f : ℝ → ℝ) (hp: f $ x = 1/x) : bijective f := sorry
--(iv) f : R → R defined by f(x) = x^3 if the Riemann hypothesis is true, and f(x) = −x if not. [NB the is a hard unsolved problem in mathematics; nobody currently knows if it is true or false.]

--(v) (hard) f : Z → Z, f(n) = n^3 − 2*n^2 + 2*n − 1