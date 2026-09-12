import Mathlib

set_option linter.all false


















theorem fermat_theorem (n : ℕ) (hn : n > 2) :
    ¬ ∃ x y z : ℕ, x ^ n + y ^ n = z ^ n :=
  sorry
















#check 3 + 2 = 5
#check 3 + 2 = 6







theorem example0 (h : 3 + 2 = 6) : 3 + 2 = 5 :=
  sorry





-- example это теорема без имени
example (h : 3 + 2 = 6) : 3 + 2 = 5 := sorry



















/- # Пропозициональная логика -/


/- ## Импликация -/



example {P Q : Prop} (hP : P) (h : P → Q) : Q :=
  h hP





example (x y : ℚ) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
















example {P Q : Prop} (h : P → Q) (hP : P) : Q :=
  h hP


















example {P Q : Prop} (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP




example {P Q R : Prop} (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  apply hQR
  apply hPQ
  exact hP

-- `apply` для backward reasoning (изменяет цель, сохраняет контекст)
-- `apply .. at ..` для forward reasoning (изменяет контекст, сохраняет цель)
example {P Q R : Prop} (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  apply hPQ at hP
  apply hQR at hP
  exact hP

example {P Q R : Prop} (h : P → Q → R) (hPQ : P → Q) (hP : P) : R := by
  apply h
  -- 2 цели, потому что `h` это "функция двух аргументов"
  · exact hP
  · apply hPQ
    exact hP

-- тактика `have` позволяет нам доказывать вспомогательные леммы
example {P Q R : Prop} (h : P → Q → R) (hPQ : P → Q) (hP : P) : R := by
  -- `have` вводит новый факт в контекст:
  have hQ : Q := by
    -- нужно доказать `Q`
    apply hPQ
    exact hP
  -- теперь у нас есть факт `hQ : Q`
  exact h hP hQ
  -- apply h at hP
  -- apply hP at hQ
  -- exact hQ

-- `suffices` делает то же что `have` но в другом порядке:
-- сначала мы показываем как при помощи нового факта доказать цель
-- потом доказываем новый факт
-- По смыслу `suffices` отвечает фразе "достаточно показать что..."
example {P Q R : Prop} (h : P → Q → R) (hPQ : P → Q) (hP : P) : R := by
  suffices hQ : Q by
    -- здесь у нас есть факт `hQ : Q`
    apply h at hP
    apply hP at hQ
    exact hQ
  -- нужно доказать `Q`
  apply hPQ
  exact hP







example {P : Prop} : P → P :=
  fun hP => hP

-- если цель имеет вид `A → B` нужно применить `intro h` и
-- мы получим факт `h : A` в локальный контекст
-- а цель станет `B`
example {P : Prop} : P → P := by
  intro hP
  exact hP

-- `variable` добавляет аргументы для всех определений и теорем ниже
-- это позволяет не писать везде повторяющиеся аргументы
variable {P Q R : Prop}

example : (P → Q) → (Q → R) → P → R := by
  -- нужно вернуть "функцию" трех аргументов
  intro hPQ hQR hP

  -- это мы уже делали выше
  sorry


example {S T : Prop} : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intro hPR hSQ hRT hQR hS
  apply hRT
  apply hQR
  apply hSQ
  assumption

/- ## True и False -/

#check True
#check False

-- Не путать с `Bool`-ами
#check true
#check false

-- `trivial` доказывает `True` (в любом контексте)
example (h : 2 + 2 = 5) (hQ : Q → R) : True := by
  trivial

-- а если в контексте есть `False` то можно доказать что угодно
example (h : False) (h2 : 7 * 6 = 42) : 7 * 6 = 43 := by
  exfalso
  -- `exfalso` заменяет цель на `False`
  -- смысл: из лжи следует все что угодно, поэтому всегда достаточно
  -- доказать `False`
  exact h












/- ## Отрицание -/

-- В Lean отрицание `¬ P` по определению равно `P → False`
-- То есть `¬ P` верно когда из `P` можно вывести противоречие (`False`)

example (h1 : P) (h2 : ¬ P) : False := by
  -- у нас есть `h2 : ¬ P`, но `¬ P` по определению
  -- равен `P → False`
  -- тактика `change` меняет тип гипотезы на другой
  -- (по определению равный)
  change P → False at h2
  -- теперь несложно:
  apply h2
  exact h1

example : P → ¬¬P := by
  intro h1
  -- `change` можно применять и к цели
  change ((P → False) → False)
  intro h2
  -- только что делали
  -- change P → False at h2
  apply h2
  exact h1

example : ¬¬P → P := by
  intro h
  change (P → False) → False at h
  -- `by_cases hP : P` создает две цели.
  -- в одной в контекст добавляется факт `hP : P`,
  -- в другой `hP : ¬ P`
  -- смысл: разбор случаев: либо `P` верно, либо нет
  by_cases hP : P
  · exact hP
  · exfalso
    apply h
    exact hP

theorem blahh : ¬¬P → P := by
  intro h
  -- Если цель - доказать `P`, то тактика `by_contra h`
  -- добавляет `h : ¬ P` в контекст и заменяет цель на `False`
  -- смысл: доказательство от противного:
  -- "пусть это неверно, тогда ... пришли к противоречию"
  by_contra h'
  change ¬P → False at h
  exact h h'
  -- apply h
  -- exact h'

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hQ
  by_contra hP
  apply hPQ at hP
  apply hQ
  assumption

/- ## Конъюнкция -/

#check And

#check True ∧ False

-- как использовать `h : P ∧ Q` как гипотезу?
example : P ∧ (Q ∧ R) → P := by
  intro h
  -- `obtain` "вытаскивает" из `h : P ∧ Q`
  -- отдельные гипотезы `hP : P` и `hQ : Q`
  -- смысл: если известно что `P ∧ Q` верно, то известно
  -- что `P` верно и что `Q` верно
  obtain ⟨hP, hQ, hR⟩ := h
  exact hP

-- как доказывать `P ∧ Q`?
example : P → Q → P ∧ Q := by
  intro hP hQ
  -- `constructor` разбивает цель `P ∧ Q` на две цели:
  -- `P` и `Q`
  -- Смысл: Если нужно доказать `P ∧ Q`, то нужно доказать
  -- и `P`, и `Q`
  constructor
  · exact hP
  · exact hQ

#check And

example : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨hP, hQ⟩ := h
  -- cases h with
  -- | intro hP hQ =>
  constructor
  · exact hQ
  · exact hP



example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hPQ hQR
  obtain ⟨hP, -⟩ := hPQ
  obtain ⟨-, hR⟩ := hQR
  exact ⟨hP, hR⟩
  -- constructor
  -- · exact hP
  -- · exact hR



/- ## Дизъюнкция -/

#check True ∨ False

-- как доказывать `P ∨ Q`?
example : P → P ∨ Q := by
  intro hP
  -- чтобы доказать `P ∨ Q` достаточно доказать `P`
  -- тактика `left` заменяет цель `P ∨ Q` на `P`
  left
  exact hP

example : Q → P ∨ Q := by
  intro hQ
  -- чтобы доказать `P ∨ Q` достаточно доказать `Q`
  -- тактика `right` заменяет цель `P ∨ Q` на `Q`
  right
  exact hQ

#check PSum

-- как использовать гипотезу `h : P ∨ Q`?
example (h1 : P ∨ Q) (h2 : P → R) (h3 : Q → R) : R := by
  -- если известно что `P ∨ Q` верно
  -- то либо `P`, либо `Q` верно
  -- `cases h1 with h4 h5` создает заменяет текущую цель на две.
  -- В первой появляется `h4 : P`, во второй `h5 : Q`
  -- и в обоих все еще нужно доказать `R`
  -- obtain h4 | h5 := h1
  cases h1 with
  | inl h4 =>
    apply h2
    exact h4
  | inr h5 =>
    apply h3
    exact h5

example (h1 : P ∨ Q) (h2 : P → R) (h3 : Q → R) : R := by
  obtain h4 | h5 := h1
  · apply h2
    exact h4
  · apply h3
    exact h5

theorem demor : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro h
  change P ∨ Q → False at h
  constructor
  · intro hP
    apply h
    left
    exact hP
  · sorry

example : ¬(P ∧ Q) → ¬P ∨ ¬Q := by
  intro h
  change P ∧ Q → False at h
  by_contra h1
  apply demor at h1
  obtain ⟨hP, hQ⟩ := h1
  apply h
  constructor
  · sorry
  · sorry

/- ## Равносильность -/

-- `P ↔ Q` по определению равно `(P → Q) ∧ (Q → P)`
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · exact demor
  · rintro ⟨_, _⟩ (_ | _) <;> contradiction

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry


/-- "закон Пирса". Это пример тавтологии, которая содержит только импликацию,
но при этом не доказуема без исключенного третьего. -/
example : ((P → Q) → P) → P := by
  by_cases hP : P <;> by_cases hQ : Q
  · intro
    assumption
  · intro
    assumption
  · intro h
    exfalso
    solve_by_elim
    -- apply hP
    -- apply h
    -- intro
    -- assumption
  · intro h
    exfalso
    apply hP
    apply h
    intro h
    contradiction


#check False.elim
