import Mathlib

/-!
# Функции

В этой задаче нужно будет доказать и опровергнуть различные свойства функций.
-/

-- чтобы раскрывать эти определения используйте `simp` или `unfold`
#check Function.Injective
#check Function.Surjective

variable {α β γ : Type}

/-- Композиция инъективных функций инъективна.

**(25 баллов)** -/
theorem injective_comp (f : α → β) (g : β → γ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  sorry


/- Постройте контрпример к следующему утверждению: если `f` и `g ∘ f` инъективны, то и `g` инъективна.

Баллы засчитываются только если доказаны все три теоремы ниже.

**(25 баллов)** -/

def f : sorry → sorry := sorry
def g : sorry → sorry := sorry

theorem f_injective : Function.Injective f := by
  sorry

theorem gf_injective : Function.Injective (g ∘ f) := by
  sorry

theorem not_g_injective : ¬ Function.Injective g := by
  sorry


/-- Докажите что функция сюръективна тогда и только тогда, когда её можно "сокращать" справа.

Подсказка: чтобы доказать равенство функций `f₁ = f₂` примените тактику `ext x`. В контекст добавится `x`, а цель станет
`f₁ x = f₂ x`. Смысл: функции равны, если они равны на всех значениях аргумента.

**(25 баллов)** -/
theorem surjective_iff (f : α → β) :
    Function.Surjective f ↔ ∀ γ : Type, ∀ g h : β → γ, g ∘ f = h ∘ f → g = h := by
  sorry

/-- Постройте сюръекцию из `ℕ` в `ℤ`.

**(25 баллов)** -/
theorem exists_surjective_nat_to_int : ∃ f : ℕ → ℤ, Function.Surjective f := by
  sorry

-- не забудьте в конце минимизировать импорты
#min_imports
