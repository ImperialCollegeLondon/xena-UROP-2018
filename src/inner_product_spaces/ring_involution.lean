import algebra.ring data.equiv.basic

open ring

/-
structure is_ring_isom (φ : R → F) extends is_ring_hom φ := 
(isom_one : function.bijective φ)

def is_ring_auto (φ : R → R) := is_ring_isom φ   

structure is_ring_invo (φ : R → R) extends is_ring_isom φ :=
(invo_comp_self : ∀ (x : R), φ (φ x) = x)

open is_ring_invo

variables (invo : R → R) [is_ring_invo invo]

instance invo_hom (φ : R → R) [is_ring_invo φ] : is_ring_hom φ := (is_ring_invo.to_is_ring_isom _).to_is_ring_hom 
-/  

structure ring_isom (R : Type*) (F : Type*) [ring R] [ring F] extends equiv R F := 
(isom_is_hom : is_ring_hom (equiv.to_fun to_equiv))

section ring_isom

variables {R : Type*} {F : Type*} [ring R] [ring F] 

open ring_isom

def isom (Hs : ring_isom R F) := (equiv.to_fun Hs.to_equiv)

instance (Hs : ring_isom R F) : is_ring_hom (isom Hs) := ring_isom.isom_is_hom Hs 

def ring_isom.map_add (Hs : ring_isom R F) (x y : R) :
isom Hs (x + y) = isom Hs x + isom Hs y := is_ring_hom.map_add (isom Hs)

def ring_isom.map_mul (Hs : ring_isom R F) (x y : R) :
isom Hs (x * y) = isom Hs x * isom Hs y := is_ring_hom.map_mul (isom Hs)

def ring_isom.map_one (Hs : ring_isom R F) :
isom Hs (1) = 1 := is_ring_hom.map_one (isom Hs)

lemma isom_is_bijective (Hs : ring_isom R F) : 
function.bijective (isom Hs) := equiv.bijective Hs.to_equiv

lemma isom_zero (Hs : ring_isom R F) : 
isom Hs (0 : R) = 0 := 
begin
have H : ∃ (a : R), isom Hs (a) = 0,
    exact (isom_is_bijective Hs).right 0,
cases H with a H,
have He : isom Hs (a) * isom Hs (0) = 0,
    rw H,
    simp,
rw ←ring_isom.map_mul at He,
rw ring.mul_zero at He,
exact He,
end

lemma isom_zero_iff (Hs : ring_isom R F) (x : R) :
isom Hs x = 0 ↔ x = 0 := 
begin
split,
    intros H,
    rw ←isom_zero Hs at H,
    exact (function.injective.eq_iff (isom_is_bijective Hs).left).mp H,

    intros H,
    rw H,
    rw isom_zero,
end

lemma isom_neg_one (Hs : ring_isom R F) : 
isom Hs (-1 : R) = -1 := 
begin
have H2 : isom Hs (-1 + 1) = 0,
    rw neg_add_self,
    rw isom_zero,
rw ring_isom.map_add at H2,
rw add_eq_zero_iff_eq_neg at H2,
rw ring_isom.map_one at H2,
exact H2,
end

lemma isom_neg (Hs : ring_isom R F) (x : R) : 
isom Hs (-x) = -(isom Hs x) :=
begin
rw ←neg_one_mul,
rw ring_isom.map_mul,
rw isom_neg_one,
rw neg_one_mul,
end

end ring_isom

def ring_auto {R : Type*} [ring R] := ring_isom R R 

class is_ring_anti_hom {R : Type*} {F :Type*} [ring R] [ring F] (f : R → F) : Prop := 
(map_add : ∀ {x y : R}, f (x + y) = f x + f y) 
(map_mul : ∀ {x y : R}, f (x * y) = f y * f x)
(map_one : f 1 = 1)

structure ring_anti_isom (R : Type*) (F : Type*) [ring R] [ring F] extends equiv R F := 
(anti_isom_is_anti_hom : is_ring_anti_hom (equiv.to_fun to_equiv))

section ring_anti_isom 

variables {R : Type*} {F : Type*} [ring R] [ring F] 

open ring_anti_isom

def anti_isom (Hs : ring_anti_isom R F) := (equiv.to_fun Hs.to_equiv)

instance (Hs : ring_anti_isom R F) : is_ring_anti_hom (anti_isom Hs) := ring_anti_isom.anti_isom_is_anti_hom Hs 

def ring_anti_isom.map_add (Hs : ring_anti_isom R F) (x y : R) :
anti_isom Hs (x + y) = anti_isom Hs x + anti_isom Hs y := is_ring_anti_hom.map_add (anti_isom Hs) 

def ring_anti_isom.map_mul (Hs : ring_anti_isom R F) (x y : R) :
anti_isom Hs (x * y) = anti_isom Hs y * anti_isom Hs x := is_ring_anti_hom.map_mul (anti_isom Hs)

def ring_anti_isom.map_one (Hs : ring_anti_isom R F) :
anti_isom Hs (1) = 1 := is_ring_anti_hom.map_one (anti_isom Hs)

lemma anti_isom_is_bijective (Hs : ring_anti_isom R F) : 
function.bijective (anti_isom Hs) := equiv.bijective Hs.to_equiv

lemma anti_isom_zero (Hs : ring_anti_isom R F) : 
anti_isom Hs (0 : R) = 0 := 
begin
have H : ∃ (a : R), anti_isom Hs (a) = 0,
    exact (anti_isom_is_bijective Hs).right 0,
cases H with a H,
have He : anti_isom Hs (a) * anti_isom Hs (0) = 0,
    rw H,
    simp,
rw ←ring_anti_isom.map_mul at He,
rw ring.zero_mul at He,
exact He,
end

lemma anti_isom_zero_iff (Hs : ring_anti_isom R F) (x : R) :
anti_isom Hs x = 0 ↔ x = 0 := 
begin
split,
    intros H,
    rw ←anti_isom_zero Hs at H,
    exact (function.injective.eq_iff (anti_isom_is_bijective Hs).left).mp H,

    intros H,
    rw H,
    rw anti_isom_zero,
end

lemma anti_isom_neg_one (Hs : ring_anti_isom R F) : 
anti_isom Hs (-1 : R) = -1 := 
begin
have H2 : anti_isom Hs (-1 + 1) = 0,
    rw neg_add_self,
    rw anti_isom_zero,
rw ring_anti_isom.map_add at H2,
rw add_eq_zero_iff_eq_neg at H2,
rw ring_anti_isom.map_one at H2,
exact H2,
end

lemma anti_isom_neg (Hs : ring_anti_isom R F) (x : R) : 
anti_isom Hs (-x) = -(anti_isom Hs x) :=
begin
rw ←neg_one_mul,
rw ring_anti_isom.map_mul,
rw anti_isom_neg_one,
rw mul_neg_one,
end

end ring_anti_isom

def comm_ring.hom_to_anti_hom {R : Type*} {F : Type*} [comm_ring R] [comm_ring F] (f : R → F) [is_ring_hom f] :
is_ring_anti_hom f :=
{
map_add := λ {x y : R}, is_ring_hom.map_add f,
map_mul := begin intros, have He : mul x y = x * y, refl, rw He, rw mul_comm, rw is_ring_hom.map_mul f, refl, end,
map_one := is_ring_hom.map_one f, 
}

def comm_ring.anti_hom_to_hom {R : Type*} {F : Type*} [comm_ring R] [comm_ring F] (f : R → F) [is_ring_anti_hom f] :
is_ring_hom f :=
{
map_add := λ {x y : R}, is_ring_anti_hom.map_add f,
map_mul := begin begin intros, have He : mul x y = x * y, refl, rw He, rw mul_comm, rw is_ring_anti_hom.map_mul f, refl, end, end,
map_one := is_ring_anti_hom.map_one f, 
}

instance ring_isom.to_is_ring_hom {R : Type*} {F : Type*} [ring R] [ring F] (Hs : ring_isom R F) : 
is_ring_hom Hs.to_equiv.to_fun := Hs.isom_is_hom

instance ring_anti_isom.to_is_ring_anti_hom {R : Type*} {F : Type*} [ring R] [ring F] (Hs : ring_anti_isom R F) : 
is_ring_anti_hom Hs.to_equiv.to_fun := Hs.anti_isom_is_anti_hom

def comm_ring.isom_to_anti_isom {R : Type*} {F : Type*} [comm_ring R] [comm_ring F] (Hs : ring_isom R F) : 
ring_anti_isom R F := 
{
to_equiv := Hs.to_equiv,
anti_isom_is_anti_hom := comm_ring.hom_to_anti_hom (isom Hs),
}

def comm_ring.anti_isom_to_isom {R : Type*} {F : Type*} [comm_ring R] [comm_ring F] (Hs : ring_anti_isom R F) : 
ring_isom R F := 
{
to_equiv := Hs.to_equiv,
isom_is_hom := comm_ring.anti_hom_to_hom (anti_isom Hs),
}

def ring_anti_auto {R : Type*} [ring R] := ring_anti_isom R R

structure ring_invo (R : Type*) [ring R] extends ring_anti_isom R R :=
(invo_comp_self : ∀ (x : R), (equiv.to_fun to_equiv) (((equiv.to_fun to_equiv) x)) = x)

open ring_invo

section ring_invo

variables {R : Type*} [ring R]

def invo (Hi : ring_invo R) := equiv.to_fun (ring_anti_isom.to_equiv Hi.to_ring_anti_isom) 

def ring_invo.map_add (Hi : ring_invo R) (x y : R) :
invo Hi (x + y) = invo Hi (x) + invo Hi (y) := ring_anti_isom.map_add (Hi.to_ring_anti_isom) x y

def ring_invo.map_mul (Hi : ring_invo R) (x y : R) :
invo Hi (x * y) = invo Hi (y) * invo Hi (x) := ring_anti_isom.map_mul (Hi.to_ring_anti_isom) x y

def ring_invo.map_one (Hi : ring_invo R) : 
invo Hi (1 : R) = 1 := ring_anti_isom.map_one (Hi.to_ring_anti_isom) 

def invo_invo (Hi : ring_invo R) (x : R) :
invo Hi (invo Hi (x)) = x := invo_comp_self Hi x
 
lemma invo_is_bijective (Hi : ring_invo R): 
function.bijective (invo Hi) := equiv.bijective (ring_invo.to_ring_anti_isom Hi).to_equiv

lemma invo_zero (Hi : ring_invo R) : 
invo Hi (0 : R) = 0 := anti_isom_zero (Hi.to_ring_anti_isom)

lemma invo_zero_iff (Hi : ring_invo R) (x : R) :
invo Hi x = 0 ↔ x = 0 := anti_isom_zero_iff (Hi.to_ring_anti_isom) x

lemma invo_neg_one (Hi : ring_invo R) : 
invo Hi (-1 : R) = -1 := anti_isom_neg_one (Hi.to_ring_anti_isom)

lemma invo_neg (Hi : ring_invo R) (x : R) : 
invo Hi (-x) = -(invo Hi x) := anti_isom_neg (Hi.to_ring_anti_isom) x

end ring_invo

def id_is_equiv (R : Type*) : equiv R R := 
⟨id, id, begin dunfold function.left_inverse, intros, simp, end, begin dunfold function.right_inverse, dunfold function.left_inverse, intros, simp, end⟩

def id_is_isom (R : Type*) [ring R] : ring_isom R R := 
⟨id_is_equiv R, begin have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end, begin have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end, begin have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end⟩ 

def id_is_anti_isom (R : Type*) [comm_ring R] : ring_anti_isom R R := comm_ring.isom_to_anti_isom (id_is_isom R) 

def id_is_invo (R : Type*) [comm_ring R] : ring_invo R :=
⟨id_is_anti_isom R, begin have He : ((id_is_anti_isom R).to_equiv).to_fun = id, refl, rw He, simp end⟩ 
