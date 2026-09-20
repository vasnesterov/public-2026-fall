import Mathlib.Tactic

/- ## Кванторы: ∀ и ∃ -/




example : ∀ n : ℕ, n + 20 > 8 := by
  -- раньше `intro` вводило в контекст факты (например `hP : P`)
  -- также можно вводить объекты (как `n : ℕ`)
  -- на уровне теории типов это работает одинаково
  intro n
  -- `grind` это умная тактика которая доказывает
  -- "очевидные" цели в некоторых областях, в частности
  -- про натуральные/целые числа и
  -- пропозициональную логику
  grind

-- квантор `∀` - это просто (зависимая) стрелка
example : (n : ℕ) → n + 20 > 8 := by
  intro n
  grind

-- но более конвенционально писать так:
example (n : ℕ) : n + 20 > 8 := by
  grind







-- как использовать гипотезу с `∀`?

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 ≤ 4 := by
  -- это работает, ведь `∀` это просто стрелка
  change (n : ℕ) → f n ≤ 4 at hf
  apply hf

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 ≤ 4 := by
  -- `exact` тоже работает, но `n` нужно указать явно
  -- `apply` его вывел сам из типа цели
  exact hf 20

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 < 7 := by
  -- `specialize` "подставляет" конкретное выражение
  -- в квантор
  specialize hf 20
  -- дальше `lia` разберется
  lia

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 + f 30 < 9 := by
  -- можно и через `have` (или `suffices`)
  have h1 : f 20 ≤ 4 := hf 20
  have h2 : f 30 ≤ 4 := hf 30
  -- дальше `lia` разберется
  lia










-- как доказать что что-то существует?

example : ∃ x : ℕ, x^2 + x - 1 = 11 := by
  -- `use` позволяет доказать что существует `x`,
  -- обладающий некоторым свойством, предъявив
  -- такой `x`, и затем доказав что он обладает свойством
  use 2^2 - 1
  -- `norm_num` вычисляет все числовые подвыражения
  -- (без переменных)
  norm_num

example (n : ℕ) : ∃ m, m > n := by
  exact ⟨n + 1, by lia⟩

-- как использовать гипотезу с `∃`?

example (n : ℕ) (h : ∃ m, m < n) : n ≠ 0 := by
  -- гипотезы с квантором существования можно
  -- распаковывать как гипотезы с конъюнкцией
  obtain ⟨m, hm⟩ := h
  -- получили в контекст `m : ℕ` и `hm : m < n`
  -- теперь этот `m` можно использовать
  lia







/- ## Переписывание -/

example (x y z : ℕ) (hx : x = y + z) (hz : z > 5) :
    x - y > 5 := by
  -- если `hx : A = B` то `rw [hx]` заменяет все `A`
  -- в цели на `B`
  rw [hx]
  -- логично предположить что в библиотеке есть лемма
  -- (y + z) - y = z
  rw [Nat.add_sub_cancel_left]
  -- дальше просто
  exact hz

example (x y z : ℕ) (hx : x = y + z)
    (hz : z > 5) :
    x - y > 5 := by
  -- можно писать в одну строчку
  rw [hx, Nat.add_sub_cancel_left]
  exact hz

#eval (5 : ℕ) - (10 : ℕ)

-- `rw` можно использовать с леммами с доп. условиями
-- (говоря формально `h` может иметь тип `P₁ → P₂ → ... → A = B`,
-- и тогда `Pᵢ` станут новыми целями)
example (x y : ℕ) (h : x + y = 12) (hy : y ≥ 2) :
    x + (y - 2) = 10 := by
  -- в библиотеке есть лемма `Nat.add_sub_assoc`:
  -- k ≤ m → n + m - k = n + (m - k)
  -- знак `←` означает "переписывай справа налево", т.е.
  -- заменяй `B` на `A`
  rw [← Nat.add_sub_assoc]
  -- после этого 2 цели: одна - переписанная старая,
  -- вторая -- доп. условие леммы (`2 ≤ y`)
  · rw [h]
  · exact hy

-- переписывать можно не только с помощью равенств,
-- но и с помощью эквивалентностей (`↔`)
-- (P.S.: но больше ни с чем, только `=` и `↔`)
example (P Q R S : Prop) (hPR : P ↔ R) (hQS : Q ↔ S) (h : P ∧ ¬ Q) : R ∧ ¬ S := by
  -- `at` позволяет переписать в гипотезе
  rw [hPR, hQS] at h
  exact h

/-
`simp` работает как `rw`, но кроме переданных ему лемм (которых вообще может не быть) он использует леммы
вида `A = B` или `A ↔ B` из библиотеки помеченные атрибутом `@[simp]`. Если какое-то подвыражение текущей цели
совпадает с левой частью в лемме, то она заменяется на правую часть. Цель тактики `simp` -- привести
выражение к "нормальной форме" насколько это возможно. Например есть `simp`-леммы
в которых доказано `|1| = 1`, `p ∧ True ↔ p`, `List.length List.nil = 0`, `x ∈ {y | P y} ↔ P x` и т.п.
Применяя `simp` к выражениям, содержащим левые части этих лемм, мы упрощаем эти выражения и с ними становится
легче работать.

Подробнее можно прочитать в секциях Rewriting и Using the Simplifier здесь:
https://leanprover.github.io/theorem_proving_in_lean4/Tactics/#Theorem-Proving-in-Lean-4--Tactics
-/

#check Nat.add_sub_cancel_left

example (x y z : ℕ) (hx : x = y + z) (hz : z > 5) :
    x - y > 5 := by
  simp only [hx, add_tsub_cancel_left, gt_iff_lt]
  -- `simp` сам применил `Nat.add_sub_cancel_left`
  exact hz

example (n : ℕ) : List.range 0 ++ ([] ++ [(n + 1) * 0]).reverse = [n - n] := by
  simp

example (n : ℕ) : n + 1 = 1 + n := by
  simp













example : ∀ n m, n + m = 0 → n = 0 := by
  sorry

example (f : ℤ → ℤ) (h : ∀ n, n < f n) : 4 < f (f 3) := by
  sorry

example {α : Type} (P : α → Prop) (h : ∃ a, ¬ P a) : ¬ ∀ a, P a := by
  sorry

example : ∃ n : ℕ, n ^ 2 + n + 1 = 7 := by
  sorry


/- ## Индукция -/

example (n : ℕ) : n = 0 ∨ ∃ m, n = m + 1 := by
  -- тактика `cases` позволяет делать разбор
  -- случаев: либо `n = 0` либо `n = m + 1` для некоторого `m`
  cases n with
  | zero =>
    -- здесь `n` заменилось на `0` во всем контексте
    left
    rfl
  | succ k =>
    -- здесь `n` заменилось на `k + 1` во всем контексте
    right
    use k

example (n : ℕ) : n = 0 ∨ ∃ m, n = m + 1 := by
  -- компактный вариант через `obtain`
  obtain _ | k := n
  · left
    rfl
  · right
    use k

def mySum (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | m + 1 => mySum m + (m + 1)

#eval mySum 3

-- факториал из Mathlib: `Nat.factorial`; после `open scoped Nat`
-- доступна нотация `n !`
open scoped Nat

#eval 5 !

example (n : ℕ) : n ! ≤ n ^ n := by
  -- `induction` позволяет рассуждать по индукции
  -- синтаксически похожа на `cases` но в каждом "рекурсивном"
  -- случае в контексте появляются индуктивные гипотезы
  induction n with
  | zero =>
    -- база индукции
    simp
  | succ m ih =>
    -- переход
    rw [Nat.factorial_succ, Nat.pow_succ, Nat.mul_comm]
    gcongr
    grw [ih]
    gcongr
    simp

/-

∃  ≈  A × B ≈ ∧
∀  ≈ ->

-/

-- вместо `induction` можно использовать рекурсию, как
-- в функциях - сослаться на доказываемую теорему.
-- Lean проверит что рекурсия корректная и примет
-- доказательство
theorem factorial_le_pow (n : ℕ) : n ! ≤ n ^ n := by
  cases n with
  | zero =>
    simp
  | succ m =>
    rw [Nat.factorial_succ, Nat.pow_succ, Nat.mul_comm]
    apply Nat.mul_le_mul_right
    trans m ^ m
    · exact factorial_le_pow m
    · apply Nat.pow_le_pow_left
      lia


example (f : ℕ → ℕ) (h : ∀ n, f n < f (n + 1)) :
    ∀ n, n ≤ f n := by
  intro n
  induction n with
  | zero =>
    simp
  | succ m ih =>
    specialize h m
    suffices hm : m < f (m + 1) by
      rwa [Nat.add_one_le_iff]
    -- exact lt_of_le_of_lt ih h
    calc
      _ ≤ f m := by
        exact ih
      _ < _ := h


/- ## Сильная индукция -/

-- ∀ m < n, P ====> ∀ m, m < n → P

theorem coins (n : ℕ) (hn : n ≥ 12) : ∃ a b, n = 4 * a + 5 * b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 16
    · -- базовые случаи: 12, 13, 14, 15
      -- `interval_cases` перебирает все значения `n`
      -- между известными границами
      interval_cases n
      · use 3, 0
      · use 2, 1
      · use 1, 2
      · use 0, 3
    · -- `n ≥ 16`: применяем гипотезу к `n - 4`
      obtain ⟨a, b, hab⟩ := ih (n - 4) (by lia) (by lia)
      use a + 1, b, by lia

-- через рекурсию сильная индукция получается "бесплатно":
-- можно ссылаться на теорему для любого меньшего аргумента,
-- Lean сам проверит что `n - 4 < n`
theorem coins' (n : ℕ) (hn : n ≥ 12) : ∃ a b, n = 4 * a + 5 * b := by
  by_cases h : n < 16
  · interval_cases n
    · use 3, 0
    · use 2, 1
    · use 1, 2
    · use 0, 3
  · obtain ⟨a, b, hab⟩ := coins' (n - 4) (by lia)
    use a + 1, b, by lia

/- ## `induction ... generalizing` -/

-- `f^[n] x` -- это `f (f (... (f x)))`, `n` раз (`Function.iterate`)
#eval (fun x => 2 * x)^[3] 1

-- по определению `f^[n + 1] x = f^[n] (f x)`
#check Function.iterate_succ_apply

-- докажем что `f` можно "вынести" наружу: `f^[n] (f x) = f (f^[n] x)`
example (f : ℕ → ℕ) (n x : ℕ) : f^[n] (f x) = f (f^[n] x) := by
  revert x
  induction n with
  | zero =>
    simp
  | succ m ih =>
    intro x
    
    rw [Function.iterate_succ_apply]
    sorry

-- `generalizing x` убирает `x` из контекста перед индукцией,
-- и индуктивная гипотеза становится `∀ x, ...`
example (f : ℕ → ℕ) (n x : ℕ) : f^[n] (f x) = f (f^[n] x) := by
  induction n generalizing x with
  | zero =>
    simp
  | succ m ih =>
    -- ih : ∀ x, f^[m] (f x) = f (f^[m] x)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    rw [ih]
