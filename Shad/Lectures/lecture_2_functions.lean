import Mathlib

/-! # Функции и стрелочные типы -/























#check "Hello, world!" -- String
#eval "Hello, world!"

#check 2 + 2           -- Nat
#eval 2 + 2

#check true && false
#eval true && false    -- Bool





























def square (n : ℕ) : ℕ :=
  n * n

-- square(7)
#eval square 7

#eval square 7 + 3
#eval square (7 + 3)

#eval square "hello"




def add (x y : ℤ) := x + y

def greet (name : String) :=
  String.append "Hello " name

#eval greet "Kitty"
















#check 2 + 2
#check (2 + 2 : ℤ)

#check "Hello, world"

#check -2

#check (3e4 : ℕ)


-- ℕ
#check square 3

-- ℕ → ℕ
#check square





















def addSquares (n : ℕ) (m : ℕ) : ℕ :=
  n ^ 2 + m ^ 2


#check addSquares







-- ℕ → ℕ → ℕ
-- это
-- ℕ → (ℕ → ℕ)

#check addSquares 3 5

#check addSquares 3

#eval (addSquares 3) 5

def squareAddNine : ℕ → ℕ := addSquares 3

-- squareAddNine m = addSquares 3 m

#check squareAddNine

#eval squareAddNine 2

-- в линейной алгебре
-- x - вектор
-- fun x y ↦ (x, y) -- функция двух аргументов
-- fun y ↦ (x, y) -- функция одного аргумента













def addSquares' : ℕ → ℕ → ℕ :=
  fun n m => n * n + m * m

#check fun (n : ℕ) (m : ℕ) => n * n + m * m

#check fun (n : ℕ) => (fun (m : ℕ) => n * n + m * m)






#check ℕ
#check String
#check Type
#check Type 1
-- Type = Type 0 : Type 1 : Type 2 : ...
-- Type u - типы вселенной u

#check [1, 2, 3]

#check [(1 : ℤ), 2, 3]

#check List ℕ

-- Type → Type
#check List

#check List Type

#check [ℕ, ℤ, String]















#check (1, -1, "Lean")

#check Prod








-- ℕ → ℕ → ℕ
-- (n : ℕ) → (m : ℕ) → ℕ


-- если head : α, tail : List α
-- то
-- List.cons head tail = лист, присоединяющий head слева к tail
-- какой тип будет иметь List.cons?

-- #check List.cons : (α : Type) → α → List α → List α

#check List.cons






#check List.cons

#check List.cons 42 [1, 2, 3]

#eval @List.cons ℤ 42 [1, 2, 3]

def myCons (α : Type) (head : α)
    (tail : List α) : List α :=
  List.cons head tail
