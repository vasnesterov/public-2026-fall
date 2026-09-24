import Mathlib.Tactic.Basic
/-
Замените `sorry` ниже на корректные доказательства. Можно пользоваться
только следующими тактиками:
* `intro`
* `exact`
* `apply`
* `cases`
* `obtain`
* `constructor`
* `have`
* `suffices`
* `left`
* `right`
* `change`
* `exfalso`
* `by_cases`
* `trivial`
-/

variable {P Q R : Prop}


/-- 34 балла -/
theorem curry_uncurry : (P ∧ Q → R) ↔ (P → Q → R) := by
  sorry

/-- 33 балла -/
theorem weak_peirce (h1 : (Q → P) → P) (h2 : Q → R) (h3 : R → P) : P := by
  sorry

/-- 33 балла -/
theorem imp_iff_not_or' : (P → Q) ↔ (¬ P ∨ Q) := by
  sorry
