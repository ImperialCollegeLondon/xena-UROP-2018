/- 7. Prove that ◦ is associative. 
In other words, prove that if h:A→B and g:B→C and f:C→D then (f◦g)◦h=f◦(g◦h) (NB: these are both functions A→D).
This is a great example of a question that is dead easy once you actually figure out what it’s asking.
-/
variables {A: Type*} {B : Type*} {C : Type*} {D : Type*} {h : A → B} {g : B → C} {f : C → D}

theorem Q1007 : (f ∘ g) ∘ h = f ∘ (g ∘ h) := sorry