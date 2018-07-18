import data.set.basic
import analysis.topology.continuity

definition foo (X : Type) [topological_space X] 
  (A : set X) : topological_space A := by apply_instance 

#check subtype.topological_space

#print foo 

definition restriction {X Y : Type} (f : X → Y) (A : set X) : A → Y :=
λ a, f a.val 

example (X : Type) [topological_space X] (A : set X)
  : topological_space A := by apply_instance 

#check @is_closed_induced_iff 

#print notation ↔
#check iff 


lemma preimage_sub (X Y : Type) (f : X → Y) (C : set Y) (A : set X) : 
(restriction f A) ⁻¹' C = { a : A | a.val ∈ f⁻¹' C} := by finish 

lemma and.congr_right_iff {a b c : Prop} : (a ∧ b ↔ a ∧ c) ↔ (a → (b ↔ c)) :=
⟨λ h ha, by simp [ha] at h; exact h, and_congr_right⟩

theorem handy (X : Type) (U A B : set X) :
  U ∩ A = U ∩ B ↔ {u : U | u.val ∈ A} = {u : U | u.val ∈ B} :=
by simp [set.set_eq_def, and.congr_right_iff]

lemma restriction_closed {X Y : Type} (f : X → Y) [topological_space X] [topological_space Y]
(A : set X) (C : set Y) (HAcont : continuous (restriction f A))
(HAclosed : is_closed A) (HCclosed : is_closed C) : is_closed (f ⁻¹' C ∩ A) := begin
  have H : is_closed ((restriction f A) ⁻¹' C),
    exact continuous_iff_is_closed.1 HAcont C HCclosed,
  have H2 := is_closed_induced_iff.1 H,
  cases H2 with D HD,
  suffices : f ⁻¹' C ∩ A = D ∩ A,
    rw this,
    exact is_closed_inter HD.1 HAclosed,
  have H₂ : { a : A | a.val ∈ f⁻¹' C} = { a : A | a.val ∈ D},
    rw ←preimage_sub X Y f C A,
    rw HD.2,
    refl,
  rw set.inter_comm,
  rw set.inter_comm D A,
  rwa handy,
end 

theorem continuous_closed_union {X Y : Type} [topological_space X] 
[topological_space Y] (A B : set X) (f : X → Y) 
(Hunion : A ∪ B = set.univ) (HAclosed : is_closed A) (HBclosed : is_closed B) : 
continuous (restriction f A) → continuous (restriction f B) → continuous f := 
begin
  intros HAcont HBcont,
  apply continuous_iff_is_closed.2,
  intros C HC,
  have H : f⁻¹' C = ((f⁻¹' C) ∩ A) ∪ ((f⁻¹' C) ∩ B),
    rw ←set.inter_distrib_left,
    rw Hunion,
    exact (set.inter_univ _).symm,
  rw H,
  apply is_closed_union,
  exact restriction_closed f A C HAcont HAclosed HC,
  exact restriction_closed f B C HBcont HBclosed HC,
end 


------- Prof Buzzard 

--- Attempt to define function (f : α → β ) in terms of its restriction 
--- can generalise this proving further Pasting_Lemma - Ex 10.7 Sutherland  ( Luca )

def fun_match {X Y : Type} [topological_space X] 
[topological_space Y] {A B : set X} [topological_space A] [topological_space B]( fa : A → Y ) ( fb : B → Y ) : Prop := 
--restriction (( set.inter A B) fa ) == restriction (( set.inter A B) fb )
sorry --∀ x ∈  set.inter A B, fa x = fb x 


def fun_composer_2_closed {X Y : Type} [topological_space X] 
[topological_space Y] {A B : set X} ( fa : A → Y ) ( fb : B → Y) { HAcont : continuous fa} { HBcont : continuous fb} 
(Hunion : A ∪ B = set.univ) (HAclosed : is_closed A) (HBclosed : is_closed B) 
(Hmatch : fun_match fa fb ) : X → Y := sorry
--- λ t : X, if H : t ∈ A  then fa t else fb t

--#check λ 
constant X : Type* 
constant A : set X
constant B : set X

#check set.inter A B 