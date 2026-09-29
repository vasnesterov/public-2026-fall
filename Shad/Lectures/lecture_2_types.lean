import Mathlib

/- # Типы -/

-- Тип - это выражение которое может стоять справа от двоеточия в `x : T`

def X : Type 1 := sorry
def x : X := sorry



theorem ttf : 2 + 2 = 4 := by
  rfl

#check ttf














/- ## Структуры -/

structure Point : Type where
  x : ℤ
  y : ℤ

-- equiv. ℤ × ℤ

#check Point
#check Point.x

def pt₁ : Point :=
  {
    x := 1,
    y := 2
  }

def pt₂ : Point := ⟨-3, 4⟩

#eval Point.x pt₁


def Point.add (p₁ p₂ : Point) : Point :=
  {
    x := p₁.x + p₂.x
    y := p₁.y + p₂.y
  }

def Point.rotate (p : Point) : Point :=
  { x := p.y, y := -p.x }

def Point.add' (p₁ p₂ : Point) : Point :=
  ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩

def Point.add'' (p₁ p₂ : Point) : Point :=
  match p₁, p₂ with
  | ⟨x₁, y₁⟩, ⟨x₂, y₂⟩ => ⟨x₁ + x₂, y₁ + y₂⟩

def Point.add''' : Point → Point → Point :=
  fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => ⟨x₁ + x₂, y₁ + y₂⟩

#eval Point.add pt₁ pt₂

#eval Point.x pt₁
-- "Dot notation":
-- Если `pt₁` имеет тип `Point`, тогда `pt₁.someMethod` это
-- синтаксический сахар для `Point.someMethod pt₁`
-- (если `Point.someMethod` принимает много аргументов, то `pt₁`
-- подставляется
-- в первый из них, имеющий тип `Point`)
#eval pt₁.x

#eval pt₁.add pt₂ -- Point.add pt₁ pt₂
#eval pt₁.rotate
#eval pt₁.rotate.add pt₂



namespace Hidden

-- Поля могут зависеть друг от друга
-- Тип натуральных чисел, меньших n
structure Fin (n : ℕ) : Type where
  val : ℕ
  small : val < n -- поля могут быть доказательствами

def two : Fin 5 := {
  val := 2
  small := by
    norm_num
}

-- Фигурные скобки делают `n` и `m` неявными аргументами.
def castUp {n m : ℕ} (x : Fin n) (h : n ≤ m) : Fin m := {
  val := x.val
  small := by
    have := x.small
    lia
}

-- `n` и `m` можно не подставлять, они выводятся из типов `x` и `h`
#check castUp two (show 5 ≤ 11 by norm_num)


end Hidden

/- ## Индуктивные типы -/

namespace Hidden

inductive Bool : Type
  | tr : Bool  -- true
  | fal : Bool -- false

#check Bool

-- 1. Как создать объект типа Bool?

#check Bool.tr
#check Bool.fal

-- 2. Как разобрать объект типа Bool?

def Bool.toNat (b : Bool) : ℕ :=
  match b with
  | .tr => 1
  | .fal => 0

theorem tr_neq_fal : Bool.tr ≠ Bool.fal := by
  change _ → False
  intro h
  apply_fun Bool.toNat at h
  simp only [Bool.toNat] at h
  lia


inductive Weekday : Type
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
  | sunday : Weekday

inductive Weekday'
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

inductive Unit
  | u

inductive Empty

example (x : Unit) : True := by
  cases x
  trivial

example (x : Empty) : False := by
  cases x





#check Weekday'.monday




inductive Pixel
  | monochrome (v : Float)
  | rgb (r g b : Float)

inductive Pixel'
  | monochrome : Float → Pixel'
  | rgb : Float → Float → Float → Pixel'

#check Pixel.monochrome 0.5
#check Pixel.rgb 1.0 0.3 0.2

def Pixel.toMonochrome (c : Pixel) : Pixel :=
  match c with
  | monochrome v => monochrome v
  | rgb r g b => monochrome ((r + g + b) / 3)


structure Group (α : Type) where
  one : α
  mul : α → α → α
  inv : α → α
  mul_one : ∀ x, mul x one = x
  assoc : ∀ x y z, mul x (mul y z) = mul (mul x y) z
  mul_inv : ∀ x, mul x (inv x) = one

def groupZ : Group ℤ := {
  one := 0,
  mul := fun x y => x + y
  inv := fun x => -x
  assoc := by grind
  mul_inv := by grind
  mul_one := by grind
}

-- ℝ∞ = [-∞, +∞]

#check ℝ

inductive ExtendedReal
  | negInf : ExtendedReal
  | posInf : ExtendedReal
  | real : ℝ → ExtendedReal

#check ExtendedReal.negInf
#check ExtendedReal.real √2

def ExtendedReal.neg (x : ExtendedReal) : ExtendedReal :=
  match x with
  | .negInf => .posInf
  | .posInf => .negInf
  | .real val => .real (-val)

open ExtendedReal

theorem neg_neg (x : ExtendedReal) : x.neg.neg = x := by
  cases x with
  | negInf => rfl -- negInf.neg.neg -> posInf.neg -> negInf
  | posInf => rfl
  | real val =>
    -- (real v).neg.neg -> (real (-v)).neg -> real (-(-v))
    -- =?= real v
    -- -(-v) =?= v на ℝ
    simp [neg]

end Hidden







namespace Hidden2

inductive Nat : Type
  | zero : Nat
  | succ (n : Nat) : Nat -- n ↦ n + 1

-- succ (succ (succ ...))

#check Nat
#check Nat.zero
#check Nat.succ

#check Nat.succ (Nat.succ Nat.zero) -- 2
#check Nat.zero.succ.succ

def Nat.pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ m => m

#eval Nat.zero.succ.succ.pred

def Nat.isEven (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ m => not (Nat.isEven m)


example (n : ℕ) : n ≤ n ^ 2 := by
  induction n with
  | zero =>
    norm_num
  | succ m ih =>
    grind

-- def f (x : ℕ) : ℕ := 1 + f x

-- example (f : ℕ → ℕ) (hf : ∀ x, f x = 1 + f x) : False := by
--   specialize hf 0
--   lia






inductive List (α : Type) : Type
  | nil
  | cons (head : α) (tail : List α)

#eval List.cons 1 List.nil -- [1]
#eval List.cons 1 (List.cons 2 .nil) -- [1, 2]

def List.sum (li : List ℤ) : ℤ :=
  match li with
  | nil => 0
  | cons head tail => head + tail.sum

def List.allPositive (li : List ℤ) : Bool :=
  match li with
  | nil => true
  | cons head tail => (head > 0) && tail.allPositive

open List
example (li : List ℤ) (h : li.allPositive) : li.sum ≥ 0 := by
  induction li with
  | nil =>
    simp [sum]
  | cons head tail ih =>
    simp [sum]
    simp [allPositive] at h
    obtain ⟨h1, h2⟩ := h
    specialize ih h2
    lia


/- ## Индуктивные семейства и прочее -/


inductive Vector' (α : Type) (n : Nat) : Type
  | nil : Vector' α Nat.zero
  | cons (m : Nat) (head : α) (tail : Vector' α m) :
    Vector' α (Nat.succ m)




inductive List' (α : Type) : Type
| nil
| cons (head : α) (tail : List' α)

-- `Vector α n` - тип массивов элементов `α` фиксированной длины `n`
inductive Vector (α : Type) : Nat → Type
  | nil : Vector α Nat.zero
  | cons {m : Nat} (head : α) (tail : Vector α m) :
    Vector α m.succ

#check Vector.nil
#check Vector ℤ Nat.zero.succ

#check (Vector.nil : Vector Nat Nat.zero)
#check Vector.cons "first" (Vector.nil : Vector String Nat.zero)





mutual
  inductive Even
    | evenZero : Even
    | oddSucc (n : Odd) : Even

  inductive Odd
    | evenSucc (n : Even) : Odd
end

mutual

  def Even.toNat (e : Even) : Nat :=
    match e with
    | Even.evenZero => Nat.zero
    | Even.oddSucc n => Nat.succ (Odd.toNat n)

  def Odd.toNat (o : Odd) : Nat :=
    match o with
    | Odd.evenSucc n => Nat.succ (Even.toNat n)

end




inductive BinTree : Type
  | leaf
  | node (left : BinTree) (right : BinTree)

#eval BinTree.node .leaf .leaf


inductive Foo : Type
  | nil : Foo
  | bar (x : ℕ → Foo) : Foo


inductive Bad : Type
  | nil : Bad
  | bar (x : Bad → ℕ) : Bad

#check Unit → Nat
#check Nat


#check Foo.nil
#check Foo.bar (fun n => Foo.nil)

inductive Tree : Type
  | leaf : Tree
  | node (children : List Tree) : Tree





mutual
  inductive Treee : Type
    | leaf : Treee
    | node (children : ListTree) : Treee

  inductive ListTree
    | nil
    | cons (head : Tree) (tail : ListTree)
end

end Hidden2
