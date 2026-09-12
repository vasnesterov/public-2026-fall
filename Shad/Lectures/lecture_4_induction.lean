import Mathlib

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
  -- change (n : ℕ) → f n ≤ 4 at hf
  apply hf

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 ≤ 4 := by
  -- `exact` тоже работает, но `n` нужно указать явно
  -- `apply` его вывел сам из типа цели
  exact hf 20

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 < 7 := by
  -- `specialize` "подставляет" конкретное выражение
  -- в квантор
  specialize hf 20
  -- дальше `grind` разберется
  grind

example (f : ℕ → ℕ) (hf : ∀ n, f n ≤ 4) : f 20 + f 30 < 9 := by
  -- можно и через `have` (или `suffices`)
  have h1 : f 20 ≤ 4 := hf 20
  have h2 : f 30 ≤ 4 := hf 30
  -- дальше `grind` разберется
  grind










-- как доказать что что-то существует?

example : ∃ x : ℕ, x^2 + x - 1 = 11 := by
  -- `use` позволяет доказать что существует `x`,
  -- обладающий некоторым свойством, предъявив
  -- такой `x`, и затем доказав что он обладает свойством
  use 3
  -- `norm_num` вычисляет все числовые подвыражения
  -- (без переменных)
  norm_num

example (n : ℕ) : ∃ m, m > n := by
  use n + 1
  grind

-- как использовать гипотезу с `∃`?

example (n : ℕ) (h : ∃ m, m < n) : n ≠ 0 := by
  -- гипотезы с квантором существования можно
  -- распаковывать как гипотезы с конъюнкцией
  obtain ⟨m, hm⟩ := h
  -- получили в контекст `m : ℕ` и `hm : m < n`
  -- теперь этот `m` можно использовать
  grind







/- ## Переписывание -/

example (x y z : List String) (hx : x = y ++ z) (hz : z.length > 5) :
    x.length > 5 := by
  -- если `hx : A = B` то `rw [hx]` заменяет все `A`
  -- в цели на `B`
  rw [hx]
  -- логично предположить что в библиотеке есть лемма
  -- (y ++ z).length = y.length + z.length
  rw [List.length_append]
  -- дальше уже `grind` справится
  grind

example (x y z : List String) (hx : x = y ++ z)
    (hz : z.length > 5) :
    x.length > 5 := by
  --  можно писать в одну строчку
  rw [hx, List.length_append]
  grind

-- `rw` можно использовать с леммами с доп. условиями
-- (говоря формально `h` может иметь тип `P₁ → P₂ → ... → A = B`,
-- и тогда `Pᵢ` станут новыми целями)
example (li : List Int) (h : li.tail.length = 5) : li.length = 6 := by
  -- знак `←` означает "переписывай справа налево", т.е.
  -- заменяй `B` на `A`
  rw [← List.length_tail_add_one]
  -- после этого 2 цели: одна - переписанная старая,
  -- вторая -- доп. условие леммы (непустота листа)
  · grind
  · grind

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

#check List.length_append

example (x y z : List String) (hx : x = y ++ z) (hz : z.length > 5) :
    x.length > 5 := by
  simp [hx]
  -- `simp` сам применил `List.length_append`
  grind

example (n : ℕ) : List.range 0 ++ ([] ++ [(n + 1) * 0]).reverse = [n - n] := by
  simp

example (n : ℕ) : n + 1 = 1 + n := by
  grind













example : ∀ n m, n + m = 0 → n = 0 := by
  intro n m h
  simp at h
  grind

example (f : ℤ → ℤ) (h : ∀ n, n < f n) : 4 < f (f 3) := by
  have : 3 < f 3 := h 3
  have : 4 ≤ f 3 := by grind
  have : f 3 < f (f 3) := h _
  grind

example {α : Type} (P : α → Prop) (h : ∃ a, ¬ P a) : ¬ ∀ a, P a := by
  intro h'
  obtain ⟨a, ha⟩ := h
  specialize h' a
  contradiction

example : ∃ li : List ℕ, li.length > 2 ∧ li.reverse = li := by
  use [0, 1, 0]
  simp


/- ## Индукция -/

example (n : ℕ) : n = 0 ∨ ∃ m, n = m + 1 := by
  -- тактика `cases` синтаксически похожа на `match`
  -- (но с меньшим количеством сахара)
  -- и позволяет делать разбор случаев "поконструкторно".
  -- Работает для любого индуктивного типа (или предиката)
  cases n with
  | zero =>
    -- здесь `n` заменилось на `0` во всем контексте
    left
    rfl
  | succ m =>
    -- здесь `n` заменилось на `m + 1` во всем контексте
    right
    use m

example (n : ℕ) : n = 0 ∨ ∃ m, n = m + 1 := by
  -- компактный вариант через `obtain`
  obtain _ | m := n
  · left
    rfl
  · right
    use m

def mySum (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | m + 1 => mySum m + (m + 1)

#eval mySum 3

example (n : ℕ) : 2 * mySum n = n * (n + 1) := by
  -- `induction` позволяет рассуждать по индукции
  -- синтаксически похожа на `cases` но в каждом "рекурсивном"
  -- случае в контексте появляются индуктивные гипотезы
  induction n with
  | zero =>
    -- база индукции
    simp [mySum]
  | succ m ih =>
    -- `ih` доказывает что цель верна для `m`
    -- а нам нужно доказать для `n = m + 1`
    -- то есть совершить индуктивный шаг
    simp [mySum]
    rw [mul_add]
    rw [ih]
    grind

-- вместо `induction` можно использовать рекурсию, как
-- в функциях - сослаться на доказываемую теорему.
-- Lean проверит что рекурсия корректная и примет
-- доказательство
theorem mySum_eq (n : ℕ) : 2 * mySum n = n * (n + 1) := by
  cases n with
  | zero =>
    simp [mySum]
  | succ m =>
    simp [mySum]
    rw [mul_add, mySum_eq m]
    grind

-- все работает аналогично с другими индуктивными типами

def List.myMap {α β : Type} (f : α → β) (li : List α) : List β :=
  match li with
  | [] => []
  | hd :: tl => f hd :: List.myMap f tl

def List.myLength {α : Type} (li : List α) : Nat :=
  match li with
  | [] => 0
  | hd :: tl => List.myLength tl + 1

example {α β : Type} (f : α → β) (li : List α) :
    (li.myMap f).myLength = li.myLength := by
  induction li with
  | nil =>
    rfl
  | cons hd tl ih =>
    simp [List.myMap, List.myLength]
    exact ih







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





/-- Тип для арифметических выражений. Любое выражение это -/
inductive ArithExpr : Type
/-- Либо число -/
| num : Int → ArithExpr
/-- Либо переменная -/
| var : String → ArithExpr
/-- Либо сумма двух выражений -/
| add : ArithExpr → ArithExpr → ArithExpr
/-- Либо произведение двух выражений -/
| mul : ArithExpr → ArithExpr → ArithExpr
/-- Либо выражение с противоположным знаком -/
| neg : ArithExpr → ArithExpr
deriving BEq

def ArithExpr.eval (e : ArithExpr) (env : String → Int) : Int :=
  match e with
  | .num x => x
  | .var name => env name
  | .add e₁ e₂ => e₁.eval env + e₂.eval env
  | .mul e₁ e₂ => e₁.eval env * e₂.eval env
  | .neg e => -e.eval env

def ArithExpr.simplifyNum (e : ArithExpr) : ArithExpr :=
  match e with
  | .num x => .num x
  | .var name => .var name
  | .neg e =>
    let e' := simplifyNum e
    match e' with
    | .num x => .num (-x)
    | _ => .neg e'
  | .add e₁ e₂ =>
    let e₁' := simplifyNum e₁
    let e₂' := simplifyNum e₂
    match e₁', e₂' with
    | .num x, .num y => .num (x + y)
    | _, _ => .add e₁' e₂'
  | .mul e₁ e₂ =>
    let e₁' := simplifyNum e₁
    let e₂' := simplifyNum e₂
    match e₁', e₂' with
    | .num x, .num y => .num (x * y)
    | _, _ => .mul e₁' e₂'

theorem simplifyNum_eval_eq_eval (expr : ArithExpr) (env : String → Int) :
    expr.simplifyNum.eval env = expr.eval env := by
  sorry

/- # Числа Фибоначчи -/

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def fastFib (n : Nat) : Nat :=
  go 1 1 n
where go (x y : Nat) (stepsLeft : Nat) :=
  match stepsLeft with
  | 0 => x
  | stepsLeftNew + 1 =>
    go y (x + y) stepsLeftNew

theorem fastFib_go_eq_fibs (n stepsLeft : Nat) :
    fastFib.go (fib n) (fib (n + 1)) stepsLeft =
    fib (n + stepsLeft) := by
  -- refine Nat.strong_induction_on (n := n) ?_
  -- intro k ih
  induction stepsLeft generalizing n with
  | zero => simp [fastFib.go]
  | succ m ih =>
    simp [fastFib.go]
    specialize ih (n + 1)
    simp [fib] at ih
    rw [ih]
    congr 1
    grind

theorem fastFib_eq_fib : fastFib = fib := by
  ext n
  simp [fastFib]
  calc
    _ = fastFib.go (fib 0) (fib 1) n := by
      simp [fib]
    _ = _ := by
      simp [fastFib_go_eq_fibs 0 n]
