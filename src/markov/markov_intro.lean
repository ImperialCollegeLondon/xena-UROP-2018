/-
Copyright (c) 2018 Luca Gerolla. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luca Gerolla, Kevin Buzzard
Fundamental Group of pointed space, inverse, reparametrisation for fundamental group. 
-/
import analysis.topology.continuity
import analysis.topology.topological_space
import analysis.topology.infinite_sum
import analysis.topology.topological_structures
import analysis.topology.uniform_space
import analysis.real
import analysis.metric_space
import analysis.normed_space
import data.real.basic tactic.norm_num
import data.set.basic
import analysis.measure_theory.borel_space
import analysis.measure_theory.lebesgue_measure
import analysis.measure_theory.integration
import analysis.measure_theory.measurable_space
import analysis.measure_theory.measure_space
import data.set order.galois_connection analysis.ennreal
       analysis.measure_theory.outer_measure
import data.set.lattice

noncomputable theory


open classical set lattice filter finset function 
local attribute [instance] prop_decidable

open measure_theory
open topological_space 

--local notation `meas` := measure_theory.measure

universes u v w x


section 

variables {α : Type*} [measure_space α]
variables { μ : measure α }{ v : measure α  } {s : set α }


---- Preliminaries: Abs. cont. measures, Radon Nikodym, and indicator function (for later)

definition abs_cont ( μ : measure α  )(v : measure α ) : Prop := 
∀ (s : set α), v s = 0 → μ s = 0 

-- stronger then needed
def finite_measure ( μ : measure α ) := μ (univ : set α) < (⊤ : ennreal)


def rad_nik_property ( μ : measure α )(v : measure α ) ( f : α → ennreal) := 
  ∀ s : set α, μ s = @lintegral α { μ := v } f


structure rad_nik_der ( μ : measure α )(v : measure α ) :=
(to_fun : α → ennreal ) 
(meas : measurable to_fun )
(density_rn : rad_nik_property μ v to_fun  )

def radon_nikodym_build ( h : abs_cont μ v ) ( hf : finite_measure v ) : rad_nik_der μ v := 
  sorry 

theorem radon_nikodym_thm₂ ( h : abs_cont μ v ) ( hf : finite_measure v ) : 
    ∃ (D : rad_nik_der μ v),  rad_nik_property μ v D.to_fun := 
begin 
 existsi radon_nikodym_build h hf, exact (radon_nikodym_build h hf).3, 
end

-- indicator function  
def ind_fun ( A : set α ) { F : measurable_space α } (h : F.is_measurable A ) : simple_func α ennreal := 
{ to_fun := λ (x: α ), if x ∈ A then (1:ennreal) else (0:ennreal), 

  measurable_sn := 
  begin intro a, by_cases H : a = 1 , 
  have h₂ : (λ (x : α), ite (x ∈ A) (1 : ennreal) 0) ⁻¹' {1} = A, 
    unfold set.preimage, apply set.ext, intro x,
    have h₃ : ite (x ∈ A) (1:ennreal) 0 = (1:ennreal) ↔ x ∈ A,
      split_ifs, --or double cc
        exact ⟨ begin intro y, exact h_1 end, begin intro y, trivial end ⟩, 
        refine ⟨ _, _ ⟩, intro y, by_contradiction,  
        have j : (0:ennreal) = (1:ennreal) → false, { simp}, exact j y, 
        intro y, cc,    
  simp [ h₃], subst H, rw h₂, exact h, 
  by_cases T : a = 0, 
    { have g₁ : (λ (x : α), ite (x ∈ A) (1:ennreal) 0) ⁻¹' {a} = -A, 
      ext z, simp, subst a, split_ifs; simpa,
    rw g₁, exact is_measurable.compl h, 
    },
  have g₁ : (λ (x : α), ite (x ∈ A) (1:ennreal) 0) ⁻¹' {a} = ∅, ext z, simp, split_ifs; cc, 
  rw g₁ , exact is_measurable.empty, 
  end , 

  finite := begin unfold set.range,  
  have w : {x : ennreal | ∃ (y : α), ite (y ∈ A) (1:ennreal) 0 = x} ⊆  {(1:ennreal), 0}, 
    intro r, rw mem_set_of_eq, 
    rintro ⟨y, rfl⟩, split_ifs; simp,
  refine finite_subset _ w  ,
  simp [w], 
  end, 

}

end 


--------------
---- Random Variables, Cond. Expectations, Stochastic and Markvov Processes
--------------

section

---- Define spaces

-- Complete separable metric space
class csm_space (β : Type*) extends metric_space β , complete_space β, separable_space β 

class measurable_csm_space (β : Type*) extends csm_space β, measurable_space β 

class probability_space (α : Type*) extends measure_space α :=
( univ_one : volume (univ : set α) = 1)

----

variables {β : Type*} [measurable_space β ]{γ  : Type*} [measurable_space γ ] 


---- Random variables

/-  Should define this with measurable_csm_space β but 
need to prove ennreal is a measurable_csm_space
-/


structure random_variable (α : Type*) [probability_space α] (β : Type*) [measurable_space β ]:=
( to_fun : α → β )
( meas : measurable to_fun )

structure real_rv (α : Type*) [probability_space α] extends random_variable α ennreal  

variables {α : Type*} [probability_space α] { F : measurable_space α }

definition random_variable.comp (x : random_variable α β ) {f : β  → γ } (h : measurable f) : 
  random_variable α γ  := 
{ to_fun := f ∘ x.to_fun , 
  meas := measurable.comp x.2 h, 
}


---- Expectation and conditional expectation 

def expectation (f : α → ennreal ) := lintegral f 


def match_integ ( t : measurable_space α ) (f g : α → ennreal) { s : set α } ( h : t.is_measurable s ): Prop := 
lintegral (( ind_fun s h ).to_fun * f ) = lintegral (( ind_fun s h ).to_fun * g )


structure cond_exp ( X : random_variable α ennreal) ( t : measurable_space α ) := 
( to_fun : α → ennreal)
( aver_match : ∀ (s : set α ) (h : t.is_measurable s), match_integ t X.to_fun to_fun h ) 


---- Stochastic process 

structure stoch_process (α : Type*) [probability_space α](β : Type*) [measurable_space β ]:=
( seq : ℕ → α → β   )
( meas : ∀ n : ℕ, measurable (seq n) )

attribute [class] stoch_process

-- instance (α : Type*) [probability_space α](β : Type*) [measurable_space β ] :
--   has_coe_to_fun ( stoch_process α β ) := begin sorry end
--   --⟨ _ , stoch_process.to_fun ⟩ 


def stoch_process.comp {f : β  → γ } (h : measurable f) ( x : stoch_process α β ) : 
  stoch_process α γ := 
{ seq := λ n , f ∘ (x.seq n) , 
  meas := λ n, measurable.comp (x.2 n) h,
}

def rv_of_stoch_proc ( x : stoch_process α β ) (n : ℕ ) : random_variable α β  := 
{ to_fun := x.seq n , 
 meas := x.meas n,  
}

def rv_of_stoch_proc.comp {f : β  → γ } (h : measurable f) ( x : stoch_process α β ) (n : ℕ ) :
  random_variable α γ := 
{ to_fun :=  f ∘ (x.seq n), 
  meas := measurable.comp (x.2 n) h, 
}


----- Sigma algebras generated

def gen_from_rv (h : measurable_space β) ( X : random_variable α β) : measurable_space α := 
measurable_space.comap X.to_fun h

def gen_from_one_stoch ( n : ℕ ) ( x : stoch_process α β ) : measurable_space α := 
measurable_space.comap (x.seq n) infer_instance 

def gen_from_stoch ( n : ℕ ) ( x : stoch_process α β  ) : measurable_space α := 
⨆ k ≤ n, measurable_space.comap (x.seq n) infer_instance

----- Markov Process

def markov_property {f : β → ennreal } ( h : measurable f) ( x : stoch_process α β ) (n : ℕ ) : Prop := 
cond_exp  ( rv_of_stoch_proc.comp h x (n+1)) ( gen_from_stoch n x ) = cond_exp (rv_of_stoch_proc.comp h x (n+1)) ( gen_from_one_stoch n x )


structure markov_process extends stoch_process α β  := 
( markov : ∀ (n :ℕ) {f : β → ennreal} (h : measurable f), markov_property h (to_stoch_process) n)





end 

-- TO DO ----------------------------------------------

-- Filtration of sigma algebras

-- a.s. as function of α → Prop and measure of reference

-- Towering property of cond expectation and f measurable checking 

----- Notation of cond. expect

-- Subst a.s equality when appropriate

------ Prove uniqueness (a.s.) of cond expectation
--- conditional expectation is Radon-Nikodym derivative of (X real valued)
-- μ induced by X    : = ∫a  X dP   (a ∈ F')
-- v = P restricted to F'
-- essentially unique

