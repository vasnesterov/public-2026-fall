import Mathlib

/-! # Двоичные деревья

В этой задаче мы рассмотрим двоичные деревья как способ представлять
кусочно-постоянные функции на отрезке.
-/

noncomputable section

/-- Тип двоичных деревьев, на листьях которых написаны вещественные числа.  -/
inductive BinTree
  | leaf (value : ℝ)
  | node (left right : BinTree)

namespace BinTree

/-- Зеркальное отражение дерева -/
def reverse (t : BinTree) : BinTree :=
  match t with
  | .leaf v => .leaf v
  | .node l r => .node r.reverse l.reverse

/-- Докажите, что дважды отзеркалив дерево, мы вернем его в изначальный вид.

**(25 баллов)** -/
theorem reverse_reverse (t : BinTree) : t.reverse.reverse = t := by
  sorry

/-- При помощи таких деревьев можно представлять кусочно-постоянные функции на отрезке.

Двумерное обобщение (https://en.wikipedia.org/wiki/Quadtree) используется для того чтобы сжимать фотографии:
если изображение достаточно однородное -- оно представляется одноцветным квадратом, если нет -- делится на 4 квадрата
и рекурсивно вызывается на них.

`t.eval : ℝ → ℝ` это функция "аппроксимированная" бинарным деревом. Математически она определена на отрезке `[0, 1]`, но
здесь для простоты мы определяем её на всем `ℝ`. -/
def eval (t : BinTree) (x : ℝ) : ℝ :=
  match t with
  | .leaf value => value
  | .node l r =>
    if x < 2⁻¹ then
      l.eval (2 * x)
    else if 2⁻¹ < x then
      r.eval (2 * x - 1)
    else
      (l.eval 1 + r.eval 0) / 2

/-- Докажите связь между `reverse` и `eval`.

**(25 баллов)**  -/
theorem reverse_eval (t : BinTree) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    t.reverse.eval x = t.eval (1 - x) := by
  sorry

/-- Определите сложение двух деревьев так, чтобы теорема ниже стала верна.
Подсказка: начните с `match x, y with`. -/
def add (x y : BinTree) : BinTree :=
  sorry

/-- Докажите что сложение деревьев представляем собой аппроксимацию суммы их функций.

**(50 баллов)** -/
theorem add_eval (t1 t2 : BinTree) (x : ℝ) : (t1.add t2).eval x = t1.eval x + t2.eval x := by
  sorry

end BinTree

-- не забудьте в конце минимизировать импорты
#min_imports
