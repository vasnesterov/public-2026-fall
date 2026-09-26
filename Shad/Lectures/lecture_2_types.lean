import Mathlib

/- # Типы -/

-- Тип - это выражение которое может стоять справа от двоеточия в `x : T`

def X : Type 1 := sorry
def x : X := sorry


/- ## Структуры -/

structure Point : Type where
  x : ℤ
  y : ℤ

#check Point
#check Point.x

def pt₁ : Point :=
  {
    x := 1
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

#eval pt₁.add pt₂
#eval pt₁.rotate
#eval (pt₁.rotate).add pt₂



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
#check castUp two (show 5 ≤ 10 by norm_num)


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

def Bool.toℕ (b : Bool) : ℕ :=
  match b with
  | Bool.tr => 1
  | Bool.fal => 0

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
  | rgb r ggg bb => monochrome ((r + ggg + bb) / 3)


end Hidden







namespace Hidden2

inductive Nat : Type
  | zero : Nat
  | succ (n : Nat) : Nat -- n ↦ n + 1

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
  | succ m => !(Nat.isEven m)

inductive List (α : Type) : Type
  | nil
  | cons (head : α) (tail : List α)

#eval List.cons 1 List.nil
#eval List.cons 1 (List.cons 2 .nil)

def List.sum (li : List ℤ) : ℤ :=
  match li with
  | nil => 0
  | cons head tail => head + tail.sum




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
