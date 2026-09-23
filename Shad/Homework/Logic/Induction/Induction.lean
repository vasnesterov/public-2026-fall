import Mathlib.Tactic

/-
Замените `sorry` ниже на корректные доказательства.

Тактика `grind` запрещена, но для рассуждений в `ℕ` можно использовать мощную тактику `omega`.
-/

/-
Принцип полной индукции. Докажите его при помощи обычной индукции.
В Mathlib он называется Nat.strong_induction_on (пригодится дальше)

25 баллов
--/
theorem Nat.strong_induction_from_simple {p : ℕ → Prop} (n : ℕ)
    (h : ∀ (n : ℕ), (∀ m < n, p m) → p n) : p n := by
  sorry

/--
"Принцип минимального элемента": если множество P ⊆ ℕ непусто, то в P есть минимальный элемент
Подсказка: используйте Nat.strong_induction_on

25 баллов
-/
theorem Nat.well_founded {P : ℕ → Prop} (h : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x ≤ y := by
  sorry

/--
Подсказка: используйте Nat.le_induction (в документации к ней написано как)

25 баллов
-/
theorem Nat.mono_of_mono_succ {α : Type} (f : ℕ → α) [LinearOrder α] (hf : ∀ n, f n ≤ f (n + 1))
    (n m : ℕ) (h : n ≤ m) :
    f n ≤ f m := by
  sorry

/--
Математический смысл: пусть `f : ℕ → ℕ`, которая:
1. В нуле равна нулю
2. Растет медленно: ∀ n, f (n + 1) ≤ f n + 1
3. Неограничена: то есть для любого `C` существует `x` такое, что `f x ≥ C`

Тогда она принимает все возможные значения.

25 баллов
-/
theorem Nat.surjective_of_unbounded (f : ℕ → ℕ) (hf₀ : f 0 = 0) (hf : ∀ n, f (n + 1) ≤ f n + 1)
    (h : ∀ C, ∃ x, f x ≥ C) : ∀ y, ∃ x, f x = y := by
  sorry
