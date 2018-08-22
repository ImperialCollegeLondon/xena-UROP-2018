import categories.category
import categories.isomorphism
import categories.tactics
import categories.functor
import categories.Ndefs
open categories categories.isomorphism categories.functor categories.idempotent tactic

--delaration of universes and variables
universes u v u₁ v₁
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

lemma Split_Idem_is_Idem (X : C) (e : X ⟶ X) : (is_Split_Idempotent e) → (is_Idempotent e) :=
begin
    intro hsi,
    cases (classical.indefinite_description _ hsi) with f hf,
    cases (classical.indefinite_description _ hf) with g hg,
    exact calc
        e ≫ e = (f ≫ g) ≫ f ≫ g : by rw hg.1
        ... = f ≫ g ≫ f ≫ g : by rw category.associativity_lemma
        ... = f ≫ (g ≫ f) ≫ g : by rw category.associativity_lemma
        ... = f ≫ 𝟙X ≫ g : by rw hg.2
        ... = f ≫ g : by rw category.left_identity_lemma
        ... =  e : by rw hg.1
end
