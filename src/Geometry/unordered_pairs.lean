universe u

private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
(p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

local infix `~` := eqv

open or

private theorem eqv.refl {α : Type u} : ∀ p : α × α, p ~ p :=
assume p, inl ⟨rfl, rfl⟩

private theorem eqv.symm {α : Type u} : ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
| (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
| (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

private theorem eqv.trans {α : Type u} : ∀ p₁ p₂ p₃ : α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
| (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
  inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
| (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
  inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
| (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
  inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
| (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
  inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

private theorem is_equivalence (α : Type u) : equivalence (@eqv α) :=
mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

instance uprod.setoid (α : Type u) : setoid (α × α) :=
setoid.mk (@eqv α) (is_equivalence α)

definition uprod (α : Type u) : Type u :=
quotient (uprod.setoid α)

namespace uprod
  definition mk {α : Type u} (a₁ a₂ : α) : uprod α :=
  ⟦(a₁, a₂)⟧

  local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂

  theorem mk_eq_mk {α : Type} (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  quot.sound (inr ⟨rfl, rfl⟩)

  private definition mem_fn {α : Type} (a : α) :
    α × α → Prop
  | (a₁, a₂) := a = a₁ ∨ a = a₂

  -- auxiliary lemma for proving mem_respects
  private lemma mem_swap {α : Type} {a : α} :
    ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
  | (a₁, a₂) := propext (iff.intro
      (λ l : a = a₁ ∨ a = a₂,
        or.elim l (λ h₁, inr h₁) (λ h₂, inl h₂))
      (λ r : a = a₂ ∨ a = a₁,
        or.elim r (λ h₁, inr h₁) (λ h₂, inl h₂)))

  private lemma mem_respects {α : Type} :
    ∀ {p₁ p₂ : α × α} (a : α),
      p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂) (b₁, b₂) a (inl ⟨a₁b₁, a₂b₂⟩) :=
    by { dsimp at a₁b₁, dsimp at a₂b₂, rw [a₁b₁, a₂b₂] }
  | (a₁, a₂) (b₁, b₂) a (inr ⟨a₁b₂, a₂b₁⟩) :=
    by { dsimp at a₁b₂, dsimp at a₂b₁, rw [a₁b₂, a₂b₁],
          apply mem_swap }

  def mem {α : Type} (a : α) (u : uprod α) : Prop :=
  quot.lift_on u (λ p, mem_fn a p) (λ p₁ p₂ e, mem_respects a e)

  local infix `∈` := mem

  theorem mem_mk_left {α : Type} (a b : α) : a ∈ {a, b} :=
  inl rfl

  theorem mem_mk_right {α : Type} (a b : α) : b ∈ {a, b} :=
  inr rfl

  theorem mem_or_mem_of_mem_mk {α : Type} {a b c : α} :
    c ∈ {a, b} → c = a ∨ c = b :=
  λ h, h
end uprod
