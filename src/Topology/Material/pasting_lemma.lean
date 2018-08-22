import data.set.basic
import analysis.topology.continuity

definition foo (X : Type*) [topological_space X] 
  (A : set X) : topological_space A := by apply_instance 

#check subtype.topological_space

#print foo 

definition restriction {X Y : Type*} (f : X → Y) (A : set X) : A → Y :=
λ a, f a.val 

example (X : Type) [topological_space X] (A : set X)
  : topological_space A := by apply_instance 

#check @is_closed_induced_iff 

#print notation ↔
#check iff 


lemma preimage_sub (X Y : Type*) (f : X → Y) (C : set Y) (A : set X) : 
(restriction f A) ⁻¹' C = { a : A | a.val ∈ f⁻¹' C} := by finish 

lemma and.congr_right_iff {a b c : Prop} : (a ∧ b ↔ a ∧ c) ↔ (a → (b ↔ c)) :=
⟨λ h ha, by simp [ha] at h; exact h, and_congr_right⟩

theorem handy (X : Type*) (U A B : set X) :
  U ∩ A = U ∩ B ↔ {u : U | u.val ∈ A} = {u : U | u.val ∈ B} :=
by simp [set.set_eq_def, and.congr_right_iff]

lemma restriction_closed {X Y : Type*} (f : X → Y) [topological_space X] [topological_space Y]
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

theorem continuous_closed_union {X Y : Type*} [topological_space X] 
[topological_space Y] {A B : set X} (f : X → Y) 
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
--- can generalise this proving further Pasting_Lemma - Ex 10.7 Sutherland  ( Luca )


---- Mario Carneiro (21/07/2018) help

--- Attempt to define function (f : α → β ) in terms of its restriction 


-- check two restrictions match
def match_of_fun {X Y} {A B : set X} (fa : A → Y) (fb : B → Y) : Prop :=
∀ x h₁ h₂, fa ⟨x, h₁⟩ = fb ⟨x, h₂⟩

local attribute [instance] classical.prop_decidable

-- define function of pasted restrictions
noncomputable def paste {X Y} {A B : set X} (Hunion : A ∪ B = set.univ) (fa : A → Y) (fb : B → Y) (t : X) : Y :=
if h₁ : t ∈ A then fa ⟨t, h₁⟩ else 
have t ∈ A ∪ B, from set.eq_univ_iff_forall.1 Hunion t,
have h₂ : t ∈ B, from this.resolve_left h₁,
fb ⟨t, h₂⟩ 

-- check paste agrees with fa
theorem paste_left {X Y} {A B : set X} (Hunion : A ∪ B = set.univ)
  (fa : A → Y) (fb : B → Y) (t : X) (h : t ∈ A) :
  paste Hunion fa fb t = fa ⟨t, h⟩ :=  dif_pos _ 

-- check paste agrees with fb
theorem paste_right {X Y} {A B : set X} (Hunion : A ∪ B = set.univ)
  (fa : A → Y) (fb : B → Y) (H : match_of_fun fa fb)
  (t : X) (h : t ∈ B) :
  paste Hunion fa fb t = fb ⟨t, h⟩ := 
by by_cases h' : t ∈ A; simp [paste, h']; apply H 

lemma rest_of_paste {X : Type* } {Y : Type*} {A B : set X} {Hunion : A ∪ B = set.univ} (fa : A → Y) (fb : B → Y)
{ f : X → Y } (H : match_of_fun fa fb) ( Hf : f = paste Hunion fa fb )  : 
fa = restriction f A ∧ fb = restriction f B := 
begin split, 
  funext, unfold restriction, rw Hf, 
  apply eq.symm _, simp [paste_left Hunion fa fb x.val x.2], 
  funext, unfold restriction, rw Hf, 
  apply eq.symm _, simp [paste_right Hunion fa fb H x.val x.2],  
end 

#print prefix subtype

#check topological_space
-- prove continuity when pasted continuous restrictions on closed sets 
theorem cont_of_paste2 {X : Type* } {Y : Type*} [topological_space X] [topological_space Y]  
{ A B : set X } { Hunion : A ∪ B = set.univ} {fa : A → Y } { fb : B → Y }
{HAclosed : is_closed A} {HBclosed : is_closed B}  { HM: match_of_fun fa fb }  
{ f : X → Y } ( Hf : f = paste Hunion fa fb ) : 
continuous fa → continuous fb → continuous f := 
begin 
intros CA CB,
have ResA : fa = (restriction f A) , exact (rest_of_paste fa fb HM Hf ).1, 
have ResB : fb = (restriction f B), exact (rest_of_paste fa fb  HM Hf ).2, 
rw ResA at CA, rw ResB at CB, 
exact continuous_closed_union f Hunion HAclosed HBclosed CA CB
end 

theorem cont_of_paste {X : Type* } {Y : Type*} [topological_space X] [topological_space Y]
{ A B : set X } { Hunion : A ∪ B = set.univ} {fa : A → Y } { fb : B → Y }
(HAclosed : is_closed A) (HBclosed : is_closed B)  ( HM : match_of_fun fa fb )
( CA : continuous fa ) ( CB : continuous fb)  : continuous (paste Hunion fa fb) := 
begin 
let f := paste Hunion fa fb, 
have Hf : f = paste Hunion fa fb, trivial, 
have ResA : fa = (restriction f A) , exact (rest_of_paste fa fb HM Hf ).1, 
have ResB : fb = (restriction f B), exact (rest_of_paste fa fb  HM Hf ).2, 
rw ResA at CA, rwa ResB at CB, 
exact continuous_closed_union f Hunion HAclosed HBclosed CA CB
end 

/- THEOREM
theorem continuous_closed_union {X Y : Type*} [topological_space X] 
[topological_space Y] {A B : set X} (f : X → Y) 
(Hunion : A ∪ B = set.univ) (HAclosed : is_closed A) (HBclosed : is_closed B) : 
continuous (restriction f A) → continuous (restriction f B) → continuous f   -/

/- RESTRICTION
definition restriction {X Y : Type*} (f : X → Y) (A : set X) : A → Y :=
λ a, f a.val  -/