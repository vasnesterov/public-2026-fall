import Mathlib

#check Set                   -- Type → Type
#check Set ℕ                 -- Type
#check {n : ℕ | gcd n 6 = 1} -- Set ℕ

-- чтобы не было коллизий имен со стандартным `Set`
namespace hidden

/-- Тип множеств элементов `α` в Lean определён так: -/
def Set (α : Type) : Type := α → Prop

/- То есть множества — это на самом деле просто предикаты на типе, и
`(x : α) ∈ (P : Set α)` — это на самом деле `P x : Prop` -/


/-
На множествах определены стандартные операции: `∪`, `∩` и т.д.
-/

def Set.union {α} (X Y : Set α) : Set α :=
  fun a ↦ X a ∨ Y a

def Set.intersection {α} (X Y : Set α) : Set α :=
  fun a ↦ X a ∧ Y a

def Set.complement {α} (X : Set α) : Set α :=
  fun a ↦ ¬ X a

/- Пустое множество и универсум -/

def Set.empty (α : Type) : Set α := fun a ↦ False

def Set.univ (α : Type) : Set α := fun a ↦ True

/- Подмножества -/

def Set.subset {α} (X Y : Set α) : Prop :=
  ∀ a, X a → Y a

end hidden

/- Рассмотрим несколько примеров того, как работать с множествами: -/

variable {α : Type} (A B C D : Set α) (x y z : α)

example : A ⊆ A := by
  change (∀ x, x ∈ A → x ∈ A) -- необязательный шаг
  intro a ha
  exact ha

example : A ⊆ B → B ⊆ C → A ⊆ C := by
  sorry

example : A ⊆ A ∪ B := by
  intro x hx
  left
  exact hx

example : A ∩ B ⊆ A := by
  intro x hx
  obtain ⟨hA, hB⟩ := hx
  exact hA

example : x ∈ (Set.univ : Set α) := by
  change True
  trivial

example : x ∈ (∅ : Set α) → False := by
  intro h
  change False at h
  exact h

-- Aᶜ означает "дополнение к A"
example : x ∈ Aᶜ → x ∉ A := by
  intro hx
  change ¬ (x ∈ A) at hx
  exact hx

-- множества можно задавать привычной `{x | ... x ...}` нотацией
example : 74 ∈ {n : ℕ | n % 2 = 0} := by
  change 74 % 2 = 0
  simp

-- чтобы доказать равенство множеств, нужно использовать тактику `ext`
example : A ∪ A = A := by
  ext x
  -- теперь цель: `x ∈ A ∪ A ↔ x ∈ A`
  constructor
  · sorry -- легко
  · sorry -- легко


variable {β γ : Type} (X Y : Set β)

def f : ℤ → ℤ := fun n ↦ 3 * n

-- `f '' X` означает образ множества под действием `f`
example : f '' {n | n % 2 = 0} = {n | n % 6 = 0} := by
  ext n
  sorry


-- `f ⁻¹' X` означает прообраз множества под действием `f`
example : id ⁻¹' X = X := by
  simp

example (f : α → β) (g : β → γ) (U : Set γ) :
    (g ∘ f) ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext x
  sorry
