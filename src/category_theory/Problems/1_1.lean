import categories.category
import categories.isomorphism
import categories.tactics
import categories.functor
import categories.ndefs
open categories
open categories.isomorphism
open categories.functor
open tactic

--delaration of universes and variables
universes u v u₁ v₁
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

-- 1a Show that identities in a category are unique
theorem uniq_id (X : C) (id' : X ⟶ X) : (∀ {A : C} (g : X ⟶ A), id' ≫ g = g) → (∀ {A : C} (g : A ⟶ X), g ≫ id' = g) → (id' = 𝟙X) :=
    begin
        intros hl hr,
        transitivity,
        symmetry,
        exact category.right_identity_lemma C id',
        exact hl(𝟙X)
    end

-- 1b Show that a morphism with both a left inverse and right inverse is an isomorphism
theorem landr_id (X Y Z : C) (f : X ⟶ Y) : (∃ gl : Y ⟶ X, gl ≫ f = 𝟙Y) → (∃ gr : Y ⟶ X, f ≫ gr = 𝟙X) → (is_Isomorphism' f) :=
    begin
    intros,
    cases (classical.indefinite_description _ a) with gl hl,
    cases (classical.indefinite_description _ a_1) with gr hr,
    apply nonempty.intro 
        (⟨gr, hr,    
            begin 
                simp,
                symmetry,
                exact calc
                𝟙Y     = gl ≫ f                : eq.symm hl
                ...    = gl ≫ 𝟙X ≫ f           : by rw category.left_identity_lemma C f
                ...    = (gl ≫ 𝟙X) ≫ f         : by rw category.associativity_lemma
                ...    = (gl ≫ (f ≫ gr)) ≫ f  : by rw hr
                ...    = ((gl ≫ f) ≫ gr) ≫ f  : by rw category.associativity_lemma C gl f gr 
                ...    = (𝟙Y ≫ gr) ≫ f         : by rw hl
                ...    = gr ≫ f                 : by rw category.left_identity_lemma C gr
            end⟩ 
        : is_Isomorphism f)
    end

-- 1c Consider f : X ⟶ Y and g : Y ⟶ Z. Show that if two out of f, g and gf are isomorphisms,then so is the third.
section Two_Out_Of_Three
    variables (X Y Z : C)
    variables (f : X ⟶ Y) (g : Y ⟶ Z)
    
    theorem tootfirsec : is_Isomorphism' f → is_Isomorphism' g → is_Isomorphism' (f ≫ g) :=
        begin
            intros hf hg,
            apply hf.elim,
            apply hg.elim,
            intros Ig If,
            exact nonempty.intro 
                ⟨Ig.1 ≫ If.1,
                begin
                    simp,
                    exact calc
                    f ≫ g ≫ Ig.1 ≫ If.1 = f ≫ (g ≫ Ig.1) ≫ If.1 : by rw category.associativity_lemma
                    ...                   = f ≫ 𝟙Y ≫ If.1          : by rw is_Isomorphism.witness_1_lemma
                    ...                   = f ≫ If.1               : by rw category.left_identity_lemma
                    ...                   = 𝟙X                      : by rw is_Isomorphism.witness_1_lemma
                end,    
                begin 
                    simp,
                    exact calc
                        Ig.1 ≫ If.1 ≫ f ≫ g  = Ig.1 ≫ (If.1 ≫ f) ≫ g : by rw category.associativity_lemma
                        ...                    = Ig.1 ≫ 𝟙Y ≫ g          : by rw is_Isomorphism.witness_2_lemma
                        ...                    = Ig.1 ≫ g               : by rw category.left_identity_lemma
                        ...                    = 𝟙Z                      : by rw is_Isomorphism.witness_2_lemma
                end⟩
        end

    theorem tootsecthi : is_Isomorphism' g → is_Isomorphism' (f ≫ g) → is_Isomorphism' f :=
        begin
            intros hg hfg,
            apply hg.elim,
            apply hfg.elim,
            intros Ifg Ig,
            exact nonempty.intro
                ⟨g ≫ Ifg.1,
                    begin
                        simp,
                        exact calc
                            f ≫ g ≫ Ifg.1 = (f ≫ g) ≫ Ifg.1 : by rw category.associativity_lemma
                            ... = 𝟙X : by rw is_Isomorphism.witness_1_lemma
                    end,
                    begin
                        simp,
                        exact calc
                            g ≫ Ifg.1 ≫ f = (g ≫ Ifg.1 ≫ f) ≫ 𝟙Y : by rw category.right_identity_lemma
                            ... = g ≫ (Ifg.1 ≫ f) ≫ 𝟙Y : by rw category.associativity_lemma
                            ... = g ≫ Ifg.1 ≫ f ≫ 𝟙Y : by rw category.associativity_lemma
                            ... = g ≫ Ifg.1 ≫ f ≫ g ≫ Ig.1 : by rw is_Isomorphism.witness_1_lemma
                            ... = g ≫ (Ifg.1 ≫ ((f ≫ g) ≫ Ig.1)) : by rw category.associativity_lemma
                            ... = g ≫ (Ifg.1 ≫ (f ≫ g)) ≫ Ig.1 : by rw (category.associativity_lemma C Ifg.1 (f ≫ g) Ig.1)
                            ... = g ≫ 𝟙Z ≫ Ig.1 : by rw is_Isomorphism.witness_2_lemma
                            ... = g ≫ Ig.1 : by rw category.left_identity_lemma
                            ... = 𝟙Y : by rw is_Isomorphism.witness_1_lemma
                    end⟩
        end
    theorem tootfirthi : is_Isomorphism' f → is_Isomorphism' (f ≫ g) → is_Isomorphism' g :=
        begin
            intros hf hfg,
            apply hf.elim,
            apply hfg.elim,
            intros Ifg If,
            exact nonempty.intro
                ⟨Ifg.1 ≫ f,
                    begin
                        simp,
                        exact calc
                            g ≫ Ifg.1 ≫ f = 𝟙Y ≫ g ≫ Ifg.1 ≫ f : by rw category.left_identity_lemma
                            ... = (If.1 ≫ f) ≫ g ≫ Ifg.1 ≫ f : by rw is_Isomorphism.witness_2_lemma
                            ... = ((If.1 ≫ f) ≫ g) ≫ Ifg.1 ≫ f : by rw (category.associativity_lemma C (If.1 ≫ f) g (Ifg.1 ≫ f))
                            ... = (If.1 ≫ (f ≫ g)) ≫ Ifg.1 ≫ f : by rw (category.associativity_lemma C If.1 f g)
                            ... = If.1 ≫ (f ≫ g) ≫ Ifg.1 ≫ f : by rw category.associativity_lemma
                            ... = If.1 ≫ ((f ≫ g) ≫ Ifg.1) ≫ f : by rw (category.associativity_lemma C (f ≫ g) Ifg.1 f)
                            ... = If.1 ≫ 𝟙X ≫ f : by rw is_Isomorphism.witness_1_lemma
                            ... = If.1 ≫ f : by rw category.left_identity_lemma
                            ... = 𝟙Y : by rw is_Isomorphism.witness_2_lemma
                    end,
                    begin
                        simp
                    end⟩
        end
end Two_Out_Of_Three

variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

-- 1d Show functors preserve isomorphisms
theorem fun_id (F : C ↝ D) (X Y : C) (f : X ⟶ Y) : (is_Isomorphism' f) → (is_Isomorphism' (F &> f)) :=
    begin
        intro hf,
        apply hf.elim,
        intro If,
        exact nonempty.intro
            /- ⟨F &> If.1,
            begin
                simp,
                exact calc
                    (F &> f) ≫ (F &> If.1) = F &> (f ≫ If.1) : by rw Functor.functoriality_lemma
                    ... = F &> 𝟙X : by rw is_Isomorphism.witness_1_lemma
                    ... = 𝟙 (F +> X) : by rw Functor.identities
            end,
            begin
                simp,
                exact calc
                    (F &> If.1) ≫ (F &> f) = F &> (If.1 ≫ f) : by rw Functor.functoriality_lemma
                    ... = F &> 𝟙Y : by rw is_Isomorphism.witness_2_lemma
                    ... = 𝟙 (F +> Y) : by rw Functor.identities
            end⟩ -/
            (isomorphism.is_Isomorphism_of_Isomorphism (F.onIsomorphisms ⟨f , If.1, by simp, by simp⟩))
    end

-- 1e Show that if F : C ↝ D is full and faithful, and F &> f : F +> A ⟶ F +> B is an isomorphism in 𝒟, then f : A ⟶ B is an isomorphism in 𝒞
theorem reflecting_isomorphisms (F : C ↝ D) (X Y : C) (f : X ⟶ Y) : is_Full_Functor F → is_Faithful_Functor F → is_Isomorphism' (F &> f) → is_Isomorphism' f :=
    begin
        intros hfu hfa hFf,
        apply hFf.elim,
        intro IFf,
        cases (classical.indefinite_description _ (hfu IFf.1)) with g hg,
        apply nonempty.intro
            (⟨g,
            begin
                simp,
                exact hfa
                    (calc
                        F &> (f ≫ g) = (F &> f) ≫ (F &> g) : by rw Functor.functoriality_lemma
                        ... = 𝟙(F +> X) : by rw [hg, is_Isomorphism.witness_1_lemma]
                        ... = F &> (𝟙X) : by rw Functor.identities
                    )
            end,
            begin
                simp,
                exact hfa
                    (calc
                        F &> (g ≫ f) = (F &> g) ≫ (F &> f) : by rw Functor.functoriality_lemma
                        ... = 𝟙(F +> Y) : by rw [hg, is_Isomorphism.witness_2_lemma]
                        ... = F &> (𝟙Y) : by rw Functor.identities
                    )
            end⟩
            : is_Isomorphism f)
    end