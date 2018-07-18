import init.algebra.group init.data.set analysis.topology.continuity 
variables {G : Type*} [group G]
def integers : set ℤ :=
set.univ
­
def Is_group {H:Type} (g:set H)  (op: H → H → H): Prop := (∀ (x y z ∈ g), op (op x y) z = op x (op y z)) ∧ 
(∃ i ∈ g , ((∀x ∈ g,op x i = x ∧ op i x = x) ∧ (∀ x ∈ g, ∃ xin ∈ g, op x xin =i ∧ op xin x =i)))
theorem int_Is_group: Is_group integers int.add:= Is_group int intA
theorem unique_identity {G:Type}(g:set G)(op: G → G → G)(i1 ∈ g)(i2 ∈ g):Is_group g op → (∀ x ∈ g,(op x i1 =x ∧  op i1 x =x  ∧ op x i2 =x ∧ op i2 x =x )) → i1 = i2 :=
begin
intros H1 H2,
have H3: i1 ∈ g,
assumption,
have A1: op i2 i1 =i2,
exact and.elim_left (H2 i2 H ),
have A2: op i2 i1 =i1,
exact and.elim_right(and.elim_right(and.elim_right ((H2 i1 H3)))),
rw[← A1],
exact A2.symm,
end
-/
def Is_subgroup {G:Type} (h:set G) (g:set G) (op: G → G → G) : Prop:= Is_group g op ∧ Is_group h op ∧ set.subset h g 
theorem groups_Sheet1_Q1: ∀(x:G), x=1 ↔ x*x=x:=
begin
intro x, 
split ,
intro H1,
rw[H1],
exact mul_one 1,
intro H2,
have H3 : x*x =x*1,
rw[ mul_one x],
exact H2,
exact mul_left_cancel H3,
end
theorem groups_Sheet1_Q2 {G:Type} (g:set G) (h1:set G) (h2:set G) (op: G → G → G):Is_group g op → set.subset h1 g → set.subset h2 g → Is_subgroup h1 g op → Is_subgroup h2 g op →  Is_subgroup (set.inter h1 h2) g op:=
begin
intros H1 H2 H3 H4 H5,
have H6: Is_group h1 op,
exact and.elim_left(and.elim_right H4),
have H7 :Is_group h2 op,
exact and.elim_left(and.elim_right H5),
unfold Is_subgroup,
split,
exact H1,
split,
unfold Is_group,
split,
intros x y z,
intros A1 A2 A3,
have A41 : x ∈ h1,
exact and.elim_left A1,
have A42 : y ∈ h1,
exact and.elim_left A2,
have A43 : z ∈ h1,
exact and.elim_left A3,
have A51: x ∈ g,
exact H2 A41,
have A52: y ∈ g,
exact H2 A42,
have A53: z ∈ g,
exact H2 A43,
have A6: ∀ (x y z ∈ g), op (op x y) z = op x (op y z),
exact and.elim_left H1,
exact  A6 x y z A51 A52 A53,
have B1: ∃ i1 ∈ h1 , (∀ x ∈ h1,op x i1 = x ∧ op x i1 = x) , 
exact H6.2.1,







end 

