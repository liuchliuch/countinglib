import Counting.Algorithm.VariableElimination.Table
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Instrumented arithmetic operations

The executable loops below accumulate the additions and multiplications they
perform, together with costs supplied by measured callbacks. Enumeration,
allocation, lookup, equality tests, and address computation are outside this
arithmetic-operation model. In particular, a plain callback wrapped with `pure`
is treated as an input-value oracle and is not assigned a machine-time bound.
-/

namespace Counting.Algorithm.VariableElimination

universe u v w

/-- A computed value together with the arithmetic operations used to obtain it. -/
structure Measured (R : Type w) where
  value : R
  additions : Nat
  multiplications : Nat
  deriving Repr

namespace Measured

variable {R : Type w}

/-- An available value carries no new arithmetic work. -/
def pure (x : R) : Measured R := ⟨x, 0, 0⟩

/-- Perform one addition and preserve both operands' recorded work. -/
def add [Add R] (x y : Measured R) : Measured R :=
  ⟨x.value + y.value, x.additions + y.additions + 1,
    x.multiplications + y.multiplications⟩

/-- Perform one multiplication and preserve both operands' recorded work. -/
def mul [Mul R] (x y : Measured R) : Measured R :=
  ⟨x.value * y.value, x.additions + y.additions,
    x.multiplications + y.multiplications + 1⟩

/-- Sum by an explicit recursion starting at zero. One addition is performed for
 every entry, including a zero-valued entry. -/
def sum [AddZeroClass R] : List (Measured R) → Measured R
  | [] => pure 0
  | x :: xs => add x (sum xs)

/-- Multiply by an explicit recursion starting at one. One multiplication is
performed for every entry, including a one-valued entry. -/
def product [MulOneClass R] : List (Measured R) → Measured R
  | [] => pure 1
  | x :: xs => mul x (product xs)

@[simp] theorem value_sum [AddZeroClass R] (xs : List (Measured R)) :
    (sum xs).value = (xs.map (·.value)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sum, add, ih]

@[simp] theorem additions_sum [AddZeroClass R] (xs : List (Measured R)) :
    (sum xs).additions = (xs.map (·.additions)).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sum, add, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem multiplications_sum [AddZeroClass R] (xs : List (Measured R)) :
    (sum xs).multiplications = (xs.map (·.multiplications)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sum, add, ih]

@[simp] theorem value_product [MulOneClass R] (xs : List (Measured R)) :
    (product xs).value = (xs.map (·.value)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [product, mul, ih]

@[simp] theorem additions_product [MulOneClass R] (xs : List (Measured R)) :
    (product xs).additions = (xs.map (·.additions)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [product, mul, ih]

@[simp] theorem multiplications_product [MulOneClass R] (xs : List (Measured R)) :
    (product xs).multiplications = (xs.map (·.multiplications)).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [product, mul, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Sum an available list of raw values, charging exactly its length additions. -/
def sumValues [AddZeroClass R] (xs : List R) : Measured R := sum (xs.map pure)

/-- Multiply an available list of raw values, charging exactly its length multiplications. -/
def productValues [MulOneClass R] (xs : List R) : Measured R := product (xs.map pure)

@[simp] theorem value_sumValues [AddZeroClass R] (xs : List R) :
    (sumValues xs).value = xs.sum := by simp [sumValues, pure, List.map_map, Function.comp_def]

@[simp] theorem additions_sumValues [AddZeroClass R] (xs : List R) :
    (sumValues xs).additions = xs.length := by simp [sumValues, pure, List.map_map, Function.comp_def]

@[simp] theorem multiplications_sumValues [AddZeroClass R] (xs : List R) :
    (sumValues xs).multiplications = 0 := by simp [sumValues, pure, List.map_map, Function.comp_def]

@[simp] theorem value_productValues [MulOneClass R] (xs : List R) :
    (productValues xs).value = xs.prod := by simp [productValues, pure, List.map_map, Function.comp_def]

@[simp] theorem additions_productValues [MulOneClass R] (xs : List R) :
    (productValues xs).additions = 0 := by simp [productValues, pure, List.map_map, Function.comp_def]

@[simp] theorem multiplications_productValues [MulOneClass R] (xs : List R) :
    (productValues xs).multiplications = xs.length := by simp [productValues, pure, List.map_map, Function.comp_def]

/-- Collect computed entries without repeating their computations. This loop adds
no coefficient arithmetic and accumulates the recorded work of each entry. -/
def collect : List (Measured R) → Measured (List R)
  | [] => pure []
  | x :: xs =>
      let tail := collect xs
      ⟨x.value :: tail.value, x.additions + tail.additions,
        x.multiplications + tail.multiplications⟩

@[simp] theorem value_collect (xs : List (Measured R)) :
    (collect xs).value = xs.map (·.value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [collect, ih]

@[simp] theorem additions_collect (xs : List (Measured R)) :
    (collect xs).additions = (xs.map (·.additions)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [collect, ih]

@[simp] theorem multiplications_collect (xs : List (Measured R)) :
    (collect xs).multiplications = (xs.map (·.multiplications)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [collect, ih]

/-- Total coefficient arithmetic operations; this excludes representation work. -/
def totalOperations (x : Measured R) : Nat := x.additions + x.multiplications

end Measured

namespace DenseTable

variable {α : Type u} {D : Type v} {R : Type w}
variable [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]

/-- Evaluate each measured callback once, store its value in the array, and
accumulate its arithmetic-operation counts while collecting the rows. -/
def tabulateMeasured (f : (α → D) → Measured R) : Measured (DenseTable α D R) :=
  let rows := Measured.collect ((enumerateAssignments α D).map f)
  ⟨⟨rows.value.toArray, by simp [rows]⟩, rows.additions, rows.multiplications⟩

@[simp] theorem value_tabulateMeasured (f : (α → D) → Measured R) :
    (tabulateMeasured f).value = tabulate (fun a => (f a).value) := by
  simp [tabulateMeasured, tabulate, List.map_map, Function.comp_def]

@[simp] theorem eval_tabulateMeasured (f : (α → D) → Measured R) (a : α → D) :
    (tabulateMeasured f).value.eval a = (f a).value := by simp

@[simp] theorem evalIndexed_tabulateMeasured (f : (α → D) → Measured R) (a : α → D) :
    (tabulateMeasured f).value.evalIndexed a = (f a).value := by simp

/-- Exact callback addition count over the materialized assignment enumeration. -/
theorem additions_tabulateMeasured_list (f : (α → D) → Measured R) :
    (tabulateMeasured f).additions =
      ((enumerateAssignments α D).map (fun a => (f a).additions)).sum := by
  simp [tabulateMeasured, List.map_map, Function.comp_def]

/-- Exact callback multiplication count over the materialized assignment enumeration. -/
theorem multiplications_tabulateMeasured_list (f : (α → D) → Measured R) :
    (tabulateMeasured f).multiplications =
      ((enumerateAssignments α D).map (fun a => (f a).multiplications)).sum := by
  simp [tabulateMeasured, List.map_map, Function.comp_def]

@[simp] theorem additions_tabulateMeasured (f : (α → D) → Measured R) :
    (tabulateMeasured f).additions = ∑ a, (f a).additions := by
  rw [additions_tabulateMeasured_list, sum_enumerateAssignments]

@[simp] theorem multiplications_tabulateMeasured (f : (α → D) → Measured R) :
    (tabulateMeasured f).multiplications = ∑ a, (f a).multiplications := by
  rw [multiplications_tabulateMeasured_list, sum_enumerateAssignments]

/-- Constant per-row addition costs scale by the exact number of rows. -/
theorem additions_tabulateMeasured_const (f : (α → D) → Measured R) (c : Nat)
    (h : ∀ a, (f a).additions = c) :
    (tabulateMeasured f).additions = (Fintype.card D ^ Fintype.card α) * c := by
  simp [h]

/-- Constant per-row multiplication costs scale by the exact number of rows. -/
theorem multiplications_tabulateMeasured_const (f : (α → D) → Measured R) (c : Nat)
    (h : ∀ a, (f a).multiplications = c) :
    (tabulateMeasured f).multiplications = (Fintype.card D ^ Fintype.card α) * c := by
  simp [h]

/-- Upper bounds on measured callback additions also compose through tabulation. -/
theorem additions_tabulateMeasured_le (f : (α → D) → Measured R) (c : Nat)
    (h : ∀ a, (f a).additions ≤ c) :
    (tabulateMeasured f).additions ≤ (Fintype.card D ^ Fintype.card α) * c := by
  rw [additions_tabulateMeasured]
  calc
    _ ≤ ∑ _ : α → D, c := Finset.sum_le_sum (fun a _ => h a)
    _ = _ := by simp

/-- Upper bounds on measured callback multiplications compose through tabulation. -/
theorem multiplications_tabulateMeasured_le (f : (α → D) → Measured R) (c : Nat)
    (h : ∀ a, (f a).multiplications ≤ c) :
    (tabulateMeasured f).multiplications ≤ (Fintype.card D ^ Fintype.card α) * c := by
  rw [multiplications_tabulateMeasured]
  calc
    _ ≤ ∑ _ : α → D, c := Finset.sum_le_sum (fun a _ => h a)
    _ = _ := by simp

end DenseTable

end Counting.Algorithm.VariableElimination
