import algebra.ring data.equiv.basic

open ring

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

structure ring_invo (R : Type*) [ring R] extends ring_isom R R :=
(invo_comp_self : ∀ (x : R), (equiv.to_fun to_equiv) (((equiv.to_fun to_equiv) x)) = x)

open ring_invo

section ring_invo

variables {R : Type*} {F : Type*} [ring R] [ring F]

def invo (Hi : ring_invo R) := equiv.to_fun(ring_isom.to_equiv (ring_invo.to_ring_isom Hi))

def ring_invo.map_add (Hi : ring_invo R) (x y : R) :
invo Hi (x + y) = invo Hi (x) + invo Hi (y) := ring_isom.map_add (Hi.to_ring_isom) x y

def ring_invo.map_mul (Hi : ring_invo R) (x y : R) :
invo Hi (x * y) = invo Hi (x) * invo Hi (y) := ring_isom.map_mul (Hi.to_ring_isom) x y

def ring_invo.map_one (Hi : ring_invo R) : 
invo Hi (1 : R) = 1 := ring_isom.map_one (Hi.to_ring_isom) 

def invo_invo (Hi : ring_invo R) (x : R) :
invo Hi (invo Hi (x)) = x := invo_comp_self Hi x
 
lemma invo_is_bijective (Hi : ring_invo R): 
function.bijective (invo Hi) := equiv.bijective (ring_invo.to_ring_isom Hi).to_equiv

lemma invo_zero (Hi : ring_invo R) : 
invo Hi (0 : R) = 0 := isom_zero (Hi.to_ring_isom)

lemma invo_zero_iff (Hi : ring_invo R) (x : R) :
invo Hi x = 0 ↔ x = 0 := isom_zero_iff (Hi.to_ring_isom) x

lemma invo_neg_one (Hi : ring_invo R) : 
invo Hi (-1 : R) = -1 := isom_neg_one (Hi.to_ring_isom)

lemma invo_neg (Hi : ring_invo R) (x : R) : 
invo Hi (-x) = -(invo Hi x) := isom_neg (Hi.to_ring_isom) x

end ring_invo

def id_is_equiv (R : Type*) : equiv R R := 
⟨id, id, begin dunfold function.left_inverse, intros, simp, end, begin dunfold function.right_inverse, dunfold function.left_inverse, intros, simp, end⟩

def id_is_isom (R : Type*) [ring R] : ring_isom R R := 
⟨id_is_equiv R, begin have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end, begin have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end, begin have He : (id_is_equiv R).to_fun = id, refl, rw He, simp end⟩ 

def id_is_invo (R : Type*) [ring R] : ring_invo R :=
⟨id_is_isom R, begin have He : ((id_is_isom R).to_equiv).to_fun = id, refl, rw He, simp end⟩ 
