import Mathlib
/-!
# Множества

В этой задаче предлагается попрактиковаться с `Set`.
-/

namespace Hidden

/-- Множество на плоскости выпукло, если для любых двух его точек `p` и `q` любая точка из отрезка
`pq` лежит в этом множестве. -/
def Convex (S : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ c ∈ Set.Icc (α := ℝ) 0 1, c • p + (1 - c) • q ∈ S

/-- **(34 балла)**

Пересечение выпуклых множеств выпукло. -/
theorem Convex.inter (A B : Set (ℝ × ℝ)) (hA : Convex A) (hB : Convex B) :
    Convex (A ∩ B) := by
  sorry

/-- **(33 балла)**

Для объединения это неверно. -/
theorem Convex.union_counterexample : ∃ A B, Convex A ∧ Convex B ∧ ¬ Convex (A ∪ B) := by
  sorry

/-- **(33 балла)**

Пусть множество натуральных чисел удовлетворяет двум условиям:
1. Оно содержит 0
2. Оно переходит внутрь себя при сдвиге на 2.

Докажите, что оно содержит множество чётных чисел.
-/
theorem subset_even (S : Set ℕ) (h0 : 0 ∈ S) (h_add : (fun n ↦ n + 2) '' S ⊆ S) :
    {x | x % 2 = 0} ⊆ S := by
  sorry

end Hidden

-- не забудьте в конце минимизировать импорты
#min_imports
