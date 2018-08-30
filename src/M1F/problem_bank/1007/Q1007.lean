open function
/- 6. (converse of 3 with added bits.)
(i) Say f : X → Y is surjective. Prove that there exists a function g : Y → X such that f ◦ g
is the identity function. Bonus point: in general, is g “natural”?
(ii) Say f : X → Y is injective. Does there always exist a function g : Y → X such that g ◦ f
is the identity function?
(iii)Say f : X → Y is any function. Does there always exist an injection g' : X → Z and a surjection h : Z → Y such that f=h◦g?
-/
variables {X: Type*} {Y : Type*} {Z : Type*} {f : X → Y} {g : Y → X} {g' : X → Z} {h : Z → Y}

-- need to say there exists though
theorem Q1007i (hp: surjective f) : f ∘ g = id := sorry 

theorem Q1007ii (hp: injective f) : (g ∘ f = id) → ff := sorry

theorem Q1007iii (hp: injective g') (hq: surjective h) : f = h ∘ g' := sorry 