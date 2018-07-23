import analysis.topology.continuity

theorem sutherland_10_6 {X : Type*} [topological_space X] {A : set X} {Z : Type*}  [topological_space Z] (g : Z → A) : 
continuous g ↔ continuous (λ z : Z, (g z).val) :=
begin
  sorry 
end 


definition ABC (X : Type*) [topological_space X] (A : set X) : topological_space A := by apply_instance 

#print ABC 

#check @subtype.topological_space

#check @continuous 

--set_option pp.implicit true
theorem sutherland_10_8 (X : Type*) [topological_space X] (A : set X) (Z : Type*) [topological_space Z]
 (g : Z → A) (Trandom : topological_space A) : 
 (@continuous Z ↥A _ Trandom g ↔ continuous (λ z : Z, (g z).val)) ↔ Trandom = subtype.topological_space

 :=
begin
  split,
  swap,
  { intro H,
    rw ←(sutherland_10_6 g),
    rw H
  },
  
end 
