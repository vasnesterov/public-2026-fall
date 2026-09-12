import Mathlib


































/- # Decidable -/

-- любой Bool конвертируется в Prop:
-- true ↦ True, false ↦ False
-- #synth Coe Bool Prop


-- обратная операция: по Prop-у понять, верен он или нет —
-- неразрешимая задача. Но в конкретных ситуациях она
-- может быть разрешимой

#check Decidable

-- namespace hidden


-- @[class]
-- inductive Decidable (p : Prop) where
--   /-- Proves that `p` is decidable by supplying a proof of `¬p` -/
--   | isFalse (h : Not p) : Decidable p
--   /-- Proves that `p` is decidable by supplying a proof of `p` -/
--   | isTrue (h : p) : Decidable p

def max (a b : Nat) : Nat :=
  if a < b then
    b
  else
    a

instance (n m : Nat) : Decidable (n < m) := sorry

/- Сравнение натуральных чисел разрешимо -/
example (n m : Nat) : Decidable (n < m) := by
  infer_instance

/- Если `P` и `Q` разрешимы, то и логические выражения от них разрешимы -/
example (P Q : Prop) [Decidable P] [Decidable Q] :
    Decidable (P ∨ Q) :=
  inferInstance

/- Проверка того, что существует `m ≤ n`, удовлетворяющий разрешимому свойству
`P` тоже разрешима (потому что это конечный перебор). -/
example (n : Nat) (P : Nat → Prop) [∀ m, Decidable (P m)] :
    Decidable (∃ m, m ≤ n ∧ P m) := by
  infer_instance

#synth Decidable (Even 3)

#eval ∃ n ≤ 6, n ^ 2 = 25

#check Nat.le


instance decideLE (n m : Nat) : Decidable (n ≤ m) :=
  match n with
  | 0 => .isTrue (by exact Nat.zero_le m)
  | k + 1 =>
    match m with
    | 0 => .isFalse (by simp)
    | l + 1 =>
      match decideLE k l with
      | .isTrue proof =>
        .isTrue (by exact Nat.add_le_add_right proof 1)
      | .isFalse proof =>
        .isFalse (by contrapose proof; exact Nat.le_of_lt_succ proof)

#eval decideLE 2 5
#reduce decideLE 2 5

example : ∃ m : ℕ, m ≤ 10 ∧ (Nat.Prime (m^2 + m)) := by
  -- тактика `decide` для цели `g` запускает поиск инстанса для
  -- `Decidable g`, и в случае успеха проверяет, что он
  -- редуцируется к `isTrue h`, и возвращает доказательство `h`
  decide

example : ¬ ∃ x ≤ 5, ∃ y ≤ 5, ∃ z ≤ 5, x ^ 2 + y ^ 2 = z ^ 2 + 1144 := by
  decide

-- выражения if-then-else как
def foo (n m : Nat) : Nat :=
  if n ≤ m then
    5
  else
    2

-- на самом деле переписываются через `Decidable`:
def foo' (n m : Nat) : Nat :=
  match decideLE n m with
  | .isTrue _ => 5
  | .isFalse _ => 2

-- `decideLE` — это инстанс `Decidable (n ≤ m)`, который находится
-- поиском инстансов

-- в общем виде как-то так:
def ite' {α : Type} (P : Prop) (ifTrue : α) (ifFalse : α)
    [inst : Decidable P] : α :=
  match inst with
  | .isTrue _ => ifTrue
  | .isFalse _ => ifFalse

-- с неразрешимыми условиями if не работает
-- потому что непонятно, как выполнять программу
def fermat (n : ℕ) : String :=
  if ∃ x y z : ℕ, x ^ n + y ^ n = z ^ n then
    "Exists!"
  else
    "Doesn't exists..."

-- но в математике можно сделать так:
open Classical in
noncomputable def fermat' (n : ℕ) : String :=
  if ∃ x y z : ℕ, x ^ n + y ^ n = z ^ n then
    "Exists!"
  else
    "Doesn't exists..."

-- в Classical есть инстанс, делающий все предикаты разрешимыми
#check Classical.propDecidable
-- но он невычислимый, поэтому всё, что его использует, тоже становится
-- noncomputable и нельзя выполнить #eval.
-- Но можно использовать в рассуждениях



example : ∃ n, n ≤ 6 ∧ ¬ Nat.Prime (2 ^ (2 ^ n) + 1) := by
  decide -- не работает

-- `decide +native` вместо `reduce (inst : Decidable p)`
-- делает `eval (inst : Decidable p)`. Поэтому он быстрее
-- но за это мы платим тем, что теперь мы верим не только
-- ядру Lean, но ещё и компилятору.
example : ∃ n, n ≤ 6 ∧ ¬ Nat.Prime (2 ^ (2 ^ n) + 1) := by
  decide +native

-- вообще верить компилятору приемлемо, если мы занимаемся
-- верификацией кода, который потом всё равно компилируем
-- этим компилятором.
-- В других случаях этого лучше избегать.


theorem th : (2^100 : ℤ) + 2^100 = 2^101 := by
  decide +native

#print axioms th

def bad : Nat := 0

@[implemented_by bad]
def good : Nat := 1

example : False := by
  have : good = 0 := by decide +native
  have : good = 1 := by rfl
  grind

-- для определённых типов есть свои тайпклассы
#check DecidableEq -- разрешимое равенство
#check DecidableLE -- разрешимое сравнение `≤`
#check DecidableRel -- разрешимое бинарное отношение `R`


instance decideExistsLt (P : Nat → Prop) [inst : ∀ n, Decidable (P n)] (m : Nat) :
    Decidable (∃ n, n < m ∧ P n) :=
  match m with
  | 0 => .isFalse (by simp)
  | k + 1 =>
    match inst k with
    | .isTrue pf =>
      .isTrue (by use k; grind)
    | .isFalse pf =>
      match decideExistsLt P k with
      | .isTrue pf1 =>
        .isTrue (by obtain ⟨a, ha⟩ := pf1; use a; grind)
      | .isFalse pf1 =>
        .isFalse (by
          contrapose pf1
          obtain ⟨a, ha1, ha2⟩ := pf1
          use a
          simp [ha2]
          have : a < k ∨ a = k := by exact Nat.lt_succ_iff_lt_or_eq.mp ha1
          obtain ha3 | ha3 := this
          · exact ha3
          · subst ha3
            contradiction
        )

example : ∀ k < 15, ∃ a ≤ k, ∃ b ≤ k, ∃ c ≤ k, ∃ d ≤ k,
    k = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  decide

-- example : ∀ k < 100, ∃ a ≤ k, ∃ b ≤ k, ∃ c ≤ k, ∃ d ≤ k,
--     k = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
--   decide +native

instance (P : Nat → Nat → Prop) [inst : ∀ n m, Decidable (P n m)] (m : Nat) :
    Decidable (∃ x y, x + y = m ∧ P x y) :=
  sorry

-- example : ∀ k ≤ 10, ∃ x y, x + y = k ∧ Nat.Prime (x^2 + y^2 + 5) := by
--   decide







/- ## Пример: max -/

namespace hidden

def max (a b : Int) : Int :=
  if a < b then
    b
  else
    a

theorem max_gt_left (a b : Int) : a ≤ max a b := by
  unfold max
  -- split_ifs разбивает ветви if-then-else на несколько подцелей
  split_ifs with h
  · exact?
  · rfl

theorem max_gt_right (a b : Int) : b ≤ max a b := by
  unfold max
  split_ifs with h
  · rfl
  · exact?

end hidden





/- # Subtype -/

namespace hidden

 -- Чётные числа можно задать как подтип `Nat`:
def Even : Type := { n : Nat // n % 2 = 0 }

-- то же самое без `{ .. // .. }`-нотации
def Even' : Type := Subtype (fun (n : Nat) => n % 2 = 0)

def two : Even := ⟨2, by simp⟩ -- второй аргумент — это доказательство 2 % 2 = 0

def two' : Even where
  val := 2
  property := by simp

-- такую функцию можно вызвать только на чётных числах, и сам возвращаемый тип
-- гарантирует нам, что результат чётный
def add (a b : Even) : Even := ⟨a.val + b.val, by grind [a.property, b.property]⟩

#eval add two two

#check Vector

end hidden


/- # Пример: exactCbrt -/

/-- Ищет кубический корень из `n` среди чисел от 0 до `m` -/
def Nat.exactCbrtHelper (n m : Nat) : Option Nat :=
  if m ^ 3 = n then
    some m
  else
    match m with
    | 0 => none
    | k + 1 => Nat.exactCbrtHelper n k

/-- Ищет кубический корень из `n` -/
def Nat.exactCbrt? (n : Nat) : Option Nat :=
  Nat.exactCbrtHelper n n

#eval Nat.exactCbrt? 27

-- мы могли бы дальше доказать, что если `Nat.exactCbrt? n = some m`, то `m ^ 3 = n`
-- и что если `Nat.exactCbrt? n = none`, то такого `m` не существует
-- это можно назвать "внешней верификацией"

-- вместо этого мы можем переплести функцию и доказательство её корректности
-- в одну сущность:

inductive ExactCbrtResult (n : Nat)
| found (res : Nat) (proof : res ^ 3 = n)
| notFound (proof : ¬ ∃ m, m ^ 3 = n)

inductive ExactCbrtHelperResult (n m : Nat)
| found (res : Nat) (proof : res ^ 3 = n)
| notFoundYet (proof : ∀ k, k ≤ m → k ^ 3 ≠ n)

def Nat.exactCbrtHelper' (n m : Nat) : ExactCbrtHelperResult n m :=
  if h : m ^ 3 = n then
    .found m h
  else
    match m with
    | 0 => .notFoundYet (by
        intro k hk
        simp at hk
        subst hk
        exact h
      )
    | k + 1 =>
      let prev := Nat.exactCbrtHelper' n k
      match prev with
      | .found res proof => .found res proof
      | .notFoundYet proof => .notFoundYet (by
          intro q hq
          by_cases hqk : q ≤ k
          · apply proof
            exact hqk
          · have hqk' : q = k + 1 := by lia
            rw [hqk']
            exact h
        )

def Nat.exactCbrt?' (n : Nat) : ExactCbrtResult n :=
  match Nat.exactCbrtHelper' n n with
  | .found res proof => .found res proof
  | .notFoundYet proof =>
    .notFound (by
      push_neg
      intro k hk
      have : k > n := by grind
      subst hk
      contrapose! this
      exact Nat.le_self_pow (by norm_num) k
    )

def Nat.exactCbrtFrontend (n : Nat) : Option Nat :=
  match Nat.exactCbrt?' n with
  | .found res proof => .some res
  | .notFound proof => .none


/- # congr -/

example (f : ℤ → ℕ) (x y : ℤ) (h : x = y) : x + x = y + y := by
  congr -- f x = f y -----> x = y

example (f : ℤ → ℤ) (g : ℤ → ℤ) (hg : ∀ n, g (g n) = n) :
    f 4 = f (g (g 3) + 1) := by
  congr
  rw [hg]
  norm_num


/- # conv -/


example (x y z : ℝ) : ∀ f : ℝ → ℝ, f (x + (y + z)) = f (x + (z + y)) := by
  -- rw [add_assoc] -- не сработает, потому что `rw` не работает под кванторами
  conv =>
    ext f
    lhs
    arg 1
    arg 2
    rw [add_comm]
  intro f
  rfl

example (x y z : ℝ) : ∀ f : ℝ → ℝ, f (x + (y + z)) = f (x + (z + y)) := by
  -- другой вариант: rw [show ... by ...]
  rw [show x + (y + z) = x + (z + y) by ring]
  intro f
  rfl



/- # fun_induction -/

def fib (n : Nat) := match n with
  | 0 => 1
  | 1 => 1
  | m + 2 => fib m + fib (m + 1)

example (n : ℕ) : fib n ≤ 2 ^ n := by
  fun_induction fib n with
  | case1 => norm_num
  | case2 => norm_num
  | case3 m ih1 ih2 =>
    calc
      fib m + fib (m + 1) ≤ 2 ^ m + fib (m + 1) := by
        gcongr -- fib m ≤ 2 ^ m
      _ ≤ 2 ^ m + 2 ^ (m + 1) := by
        gcongr
      _ = 3 * 2 ^ m := by
        rw [pow_succ]
        ring
      _ ≤ 2 ^ (m + 2) := by
        simp [pow_succ]
        ring_nf
        gcongr
        norm_num

/- # Индуктивные предикаты -/

namespace hidden

inductive Bracket
| op
| cl

-- inductive CorrectBS' : Type
-- | empty
-- | append (left : CorrectBS') (right : CorrectBS')
-- | enclose (h : CorrectBS')

-- def CorrectBS'.toList (bs : CorrectBS') : (List Bracket) := sorry

-- def CorrectBS (li : List Bracket) : Prop :=
--   ∃ bs : CorrectBS', bs.toList = li

/- Правильность скобочной последовательности -/
inductive CorrectBS : (List Bracket) → Prop
| empty : CorrectBS []
| append {left right : List Bracket}
  (h_left : CorrectBS left) (h_right : CorrectBS right) :
    CorrectBS (left ++ right)
| enclose {bs : List Bracket} (h : CorrectBS bs) :
    CorrectBS (.op :: bs ++ [.cl])

theorem empty_correct : CorrectBS [] := CorrectBS.empty

theorem op_cl_correct : CorrectBS [.op, .cl] :=
  CorrectBS.enclose empty_correct

example : CorrectBS [.op, .cl, .op, .cl] :=
  CorrectBS.append op_cl_correct op_cl_correct

example (bs : List Bracket) (h : CorrectBS bs) :
    bs.length % 2 = 0 := by
  induction h with
  | empty => simp
  | @append left right h_left h_right ih_left ih_right =>
    grind
  | @enclose bs h ih =>
    grind

/- Стандартный алгоритм проверки скобочной последовательности на правильность.
```py
def check(bs):
  balance = 0
  for b in bs:
    if b == '(':
      balance += 1
    else:
      balance -= 1
      if balance < 0:
        return False
  return balance == 0
```
Как обычно, цикл `for` переписываем через рекурсию.
-/
def check (bs : List Bracket) : Bool :=
  go bs 0
where
  go (bs : List Bracket) (balance : ℤ) : Bool :=
    match bs with
    | [] => balance == 0
    | .op :: tail =>
      go tail (balance + 1)
    | .cl :: tail =>
      if balance ≤ 0 then
        false
      else
        go tail (balance - 1)

def balance (bs : List Bracket) : ℤ :=
  bs.map (fun | .cl => -1 | .op => 1) |>.sum

theorem balance_append (left right : List Bracket) :
    balance (left ++ right) = balance left + balance right := by
  simp [balance]

theorem go_append (left right : List Bracket) (b c : ℤ) (h : check.go left b = true)
    (hc : 0 ≤ c) :
    check.go (left ++ right) (b + c) = check.go right c := by
  cases left with
  | nil =>
    simp at h ⊢
    suffices b = 0 by grind
    simp [check.go] at h
    assumption
  | cons hd tl =>
    cases hd with
    | op =>
      simp [check.go] at h ⊢
      apply go_append (c := c) (right := right) at h
      convert h using 2
      grind
    | cl =>
      simp [check.go] at h ⊢
      simp [show ¬ (b + c ≤ 0) by grind]
      obtain ⟨h1, h2⟩ := h
      apply go_append (c := c) (right := right) at h2
      specialize h2 hc
      convert h2 using 2
      grind

theorem CorrectBS.check_eq_true (bs : List Bracket) (h : CorrectBS bs) :
    check bs = true := by
  induction h with
  | empty => simp [check, check.go]
  | @append left right h_left h_right ih_left ih_right =>
    cases left with
    | nil =>
      simp
      assumption
    | cons leftHd leftTl =>
      cases leftHd with
      | op =>
        simp [check, check.go]
        conv => lhs; arg 2; change 1 + 0
        rw [go_append]
        rotate_right
        · simp
        · exact ih_right
        simp [check, check.go] at ih_left
        assumption
      | cl =>
        simp [check, check.go] at *
  | @enclose bs h ih =>
    simp [check, check.go] at *
    conv => lhs; arg 2; change 0 + 1
    rw [go_append]
    · simp [check.go]
    · assumption
    · simp

theorem CorrectBS_iff_check_eq_true (bs : List Bracket) :
    CorrectBS bs ↔ check bs = true where
  mp h := by
    apply CorrectBS.check_eq_true
    exact h
  mpr h :=
    sorry

instance (bs : List Bracket) : Decidable (CorrectBS bs) :=
  if h : check bs then
    .isTrue (by rw [CorrectBS_iff_check_eq_true]; assumption)
  else
    .isFalse (by rw [CorrectBS_iff_check_eq_true]; assumption)

example : CorrectBS [.op, .cl, .op, .cl] := by
  decide

example : ¬ CorrectBS [.op, .cl, .cl] := by
  decide

end hidden









/- # Пример: быстрая сортировка -/

#check List.Perm

namespace hidden

variable {α : Type} [LinearOrder α]


set_option pp.showLetValues true

def divide (xs : List α) (pivot : α) : List α × List α × List α :=
  let (less, notLess) := xs.partition (fun x => x < pivot)
  let (equal, greater) := notLess.partition (fun x => x = pivot)
  (less, equal, greater)

def quickSort (xs : List α) : List α :=
  if h : xs.length = 0 then
    []
  else
    have : xs.length / 2 < xs.length := by grind
    let pivot := xs[xs.length / 2]
    let (eq := h2) (less, equal, greater) := divide xs pivot
    -- match h2 : divide xs pivot with
    -- | (less, equal, greater) =>
    let lessSorted := quickSort less
    let greaterSorted := quickSort greater
    lessSorted ++ equal ++ greaterSorted
termination_by xs.length
decreasing_by
  · --have : xs.length / 2 < xs.length := by grind
    simp [divide] at h2
    replace h2 := h2.left
    rw [← h2]
    apply List.length_filter_lt_length_iff_exists.mpr
    use pivot
    simp [pivot]
  · --have : xs.length / 2 < xs.length := by grind
    simp [divide] at h2
    replace h2 := h2.right.right
    rw [← h2]
    apply List.length_filter_lt_length_iff_exists.mpr
    use pivot
    simp [pivot]

#print axioms quickSort

#eval quickSort [3, 1, 4, 1, 5]

#check List.filter_append_perm

theorem quickSort_perm (xs : List α) : List.Perm xs (quickSort xs) := by
  fun_induction quickSort xs with
  | case1 x h =>
    simp at h
    simp
    apply h
  | case2 xs h1 h2 pivot less equal greater h3 lessSorted greaterSorted
      ih_less ih_greater =>
    apply List.Perm.trans (l₂ := less ++ equal ++ greater)
    · simp [divide] at h3
      let notLess := xs.filter (fun x => !(x < pivot))
      obtain ⟨h_less, h_equal, h_greater⟩ := h3
      have : xs.Perm (less ++ notLess) := by
        symm
        simp [← h_less, notLess]
        apply List.filter_append_perm
      apply List.Perm.trans this
      simp
      apply List.Perm.append_left
      have h_equal' : equal = notLess.filter (fun x => x = pivot) := by
        simp [← h_equal, notLess]
      have h_greater' : greater = notLess.filter (fun x => !(x = pivot)) := by
        simp [← h_greater, notLess]
      rw [h_equal', h_greater']
      symm
      apply List.filter_append_perm
    · apply List.Perm.append
      · apply List.Perm.append
        · exact ih_less
        · rfl
      · exact ih_greater
