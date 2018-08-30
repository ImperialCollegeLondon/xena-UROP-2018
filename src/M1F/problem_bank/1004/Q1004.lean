open function
/- this question should read Q4 (but on the 2016/17 example sheet, this reads 3)
4. (One-sided inverses.)
(i) Say f : X → Y is a function and there exists a function g : Y → X such that f ◦ g is the identity function Y → Y . Prove that f is surjective.
(ii) Say f : X → Y is a function and there exists a function g : Y → X such that g ◦ f is the identity function X → X. Prove that f is injective.
-/
variables {X: Type*} {Y : Type*} {f : X → Y} {g : Y → X} 

theorem Q1004i : f ∘ g = id → surjective f := sorry

theorem Q1004ii : g ∘ f = id → injective f := sorry 