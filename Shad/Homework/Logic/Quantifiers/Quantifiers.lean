import Mathlib.Tactic
/-
Замените `sorry` ниже на корректные доказательства. Можно пользоваться
только следующими тактиками:
* `intro`
* `exact`
* `apply`
* `cases`
* `obtain`
* `constructor`
* `left`
* `right`
* `change`
* `exfalso`
* `by_cases`
* `by_contra`
* `use`
* `simp`
* `norm_num`
* `rw`
* `congr`
-/

-- 50 баллов
theorem exists_not_of_not_forall {α : Type} (P : α → Prop) : (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  sorry

-- 50 баллов
-- https://problems.ru/view_problem_details_new.php?id=66354
theorem func_equation (f : ℤ → ℤ) (hf : ∀ x y, f (x ^ 2 + y) = f x + f (y ^ 2)) : f (-1) = 0 := by
  sorry
