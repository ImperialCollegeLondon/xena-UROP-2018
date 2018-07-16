import init.algebra.group init.data.set
variables {G : Type*} [group G]
def Is_group {G:Type} (g:set G)  (op: G → G → G): Prop := (∀ (x y z ∈ g), op (op x y) z = op x (op y z)) ∧ 
(∃ i ∈g , (∀x ∈ g,op x i = x ∧ op i x = x) ∧ (∀ x ∈ g, ∃ xin:G, op x xin =i ∧ op xin x =i))

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
unfold Is_subgroup,
split,
exact H1,
split,
unfold Is_group,
split,
intros x y z,
intros A1 A2 A3,
--have A4: x  ∈ g ∧ y ∈ g ∧ z ∈ g,
--split,
have A41 : x ∈ h1,
exact and.elim_left A1,
have A42 : y ∈ h1,
exact and.elim_left A2,
have A43 : z ∈ h1,
exact and.elim_left A3,

have A6: ∀ (x y z ∈ g), op (op x y) z = op x (op y z),
exact and.elim_left H1,




end 

