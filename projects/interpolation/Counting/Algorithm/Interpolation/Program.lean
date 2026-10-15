import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Oracle field programs

An expression records every oracle query and every field operation used by an
interpolation algorithm. Evaluation and both resource counts are independent
structural recursions. A measured interpreter provides a second, simultaneous
semantics and is proved to agree with all three recursions.

The operation count is an arithmetic-operation count, not a bit-complexity bound.
Division is total in the field semantics; `Program.Safe` separately records that
all denominators encountered by a program are nonzero.
-/

namespace Counting.Algorithm.Interpolation

universe u v

/-- A finite expression over constants, oracle queries, and field operations. -/
inductive Program (K : Type u) (ι : Type v) : Type (max u v) where
  | constant (value : K)
  | query (index : ι)
  | add (left right : Program K ι)
  | sub (left right : Program K ι)
  | mul (left right : Program K ι)
  | div (left right : Program K ι)

namespace Program

variable {K : Type u} {ι : Type v}

/-- Executable value semantics, with the oracle supplied explicitly. -/
@[simp] def eval [Field K] (oracle : ι → K) : Program K ι → K
  | .constant value => value
  | .query index => oracle index
  | .add left right => eval oracle left + eval oracle right
  | .sub left right => eval oracle left - eval oracle right
  | .mul left right => eval oracle left * eval oracle right
  | .div left right => eval oracle left / eval oracle right

/-- Every query occurrence is charged, including repeated queries. -/
@[simp] def queries : Program K ι → ℕ
  | .constant _ => 0
  | .query _ => 1
  | .add left right => queries left + queries right
  | .sub left right => queries left + queries right
  | .mul left right => queries left + queries right
  | .div left right => queries left + queries right

/-- Each addition, subtraction, multiplication, or division node costs one. -/
@[simp] def fieldOps : Program K ι → ℕ
  | .constant _ => 0
  | .query _ => 0
  | .add left right => fieldOps left + fieldOps right + 1
  | .sub left right => fieldOps left + fieldOps right + 1
  | .mul left right => fieldOps left + fieldOps right + 1
  | .div left right => fieldOps left + fieldOps right + 1

/-- Every denominator evaluated during execution is nonzero. -/
@[simp] def Safe [Field K] (oracle : ι → K) : Program K ι → Prop
  | .constant _ => True
  | .query _ => True
  | .add left right => Safe oracle left ∧ Safe oracle right
  | .sub left right => Safe oracle left ∧ Safe oracle right
  | .mul left right => Safe oracle left ∧ Safe oracle right
  | .div left right => Safe oracle left ∧ Safe oracle right ∧ eval oracle right ≠ 0

/-- Resources measured by the interpreter. -/
structure Cost where
  queries : ℕ
  fieldOps : ℕ
  deriving DecidableEq, Repr

/-- Combining two executions and performing one binary field operation. -/
def Cost.primitive (left right : Cost) : Cost where
  queries := left.queries + right.queries
  fieldOps := left.fieldOps + right.fieldOps + 1

/-- A measured interpreter that computes values and costs in one recursion. -/
@[simp] def run [Field K] (oracle : ι → K) : Program K ι → K × Cost
  | .constant value => (value, ⟨0, 0⟩)
  | .query index => (oracle index, ⟨1, 0⟩)
  | .add left right =>
      let l := run oracle left
      let r := run oracle right
      (l.1 + r.1, Cost.primitive l.2 r.2)
  | .sub left right =>
      let l := run oracle left
      let r := run oracle right
      (l.1 - r.1, Cost.primitive l.2 r.2)
  | .mul left right =>
      let l := run oracle left
      let r := run oracle right
      (l.1 * r.1, Cost.primitive l.2 r.2)
  | .div left right =>
      let l := run oracle left
      let r := run oracle right
      (l.1 / r.1, Cost.primitive l.2 r.2)

@[simp] theorem run_value [Field K] (oracle : ι → K) (p : Program K ι) :
    (run oracle p).1 = eval oracle p := by
  induction p <;> simp_all

@[simp] theorem run_queries [Field K] (oracle : ι → K) (p : Program K ι) :
    (run oracle p).2.queries = queries p := by
  induction p <;> simp_all [Cost.primitive]

@[simp] theorem run_fieldOps [Field K] (oracle : ι → K) (p : Program K ι) :
    (run oracle p).2.fieldOps = fieldOps p := by
  induction p <;> simp_all [Cost.primitive]

/-- A right-associated sum, including one addition per list entry. -/
def listSum [Zero K] (ps : List (Program K ι)) : Program K ι :=
  ps.foldr .add (.constant 0)

/-- A right-associated product, including one multiplication per list entry. -/
def listProduct [One K] (ps : List (Program K ι)) : Program K ι :=
  ps.foldr .mul (.constant 1)

@[simp] theorem listSum_nil [Zero K] : listSum ([] : List (Program K ι)) = .constant 0 :=
  rfl

@[simp] theorem listSum_cons [Zero K] (p : Program K ι) (ps : List (Program K ι)) :
    listSum (p :: ps) = .add p (listSum ps) :=
  rfl

@[simp] theorem listProduct_nil [One K] :
    listProduct ([] : List (Program K ι)) = .constant 1 :=
  rfl

@[simp] theorem listProduct_cons [One K] (p : Program K ι) (ps : List (Program K ι)) :
    listProduct (p :: ps) = .mul p (listProduct ps) :=
  rfl

@[simp] theorem eval_listSum [Field K] (oracle : ι → K) (ps : List (Program K ι)) :
    eval oracle (listSum ps) = (ps.map (eval oracle)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

@[simp] theorem eval_listProduct [Field K] (oracle : ι → K) (ps : List (Program K ι)) :
    eval oracle (listProduct ps) = (ps.map (eval oracle)).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

@[simp] theorem queries_listSum [Zero K] (ps : List (Program K ι)) :
    queries (listSum ps) = (ps.map queries).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

@[simp] theorem queries_listProduct [One K] (ps : List (Program K ι)) :
    queries (listProduct ps) = (ps.map queries).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

@[simp] theorem fieldOps_listSum [Zero K] (ps : List (Program K ι)) :
    fieldOps (listSum ps) = (ps.map fieldOps).sum + ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih, Nat.add_assoc]

@[simp] theorem fieldOps_listProduct [One K] (ps : List (Program K ι)) :
    fieldOps (listProduct ps) = (ps.map fieldOps).sum + ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih, Nat.add_assoc]

@[simp] theorem safe_listSum [Field K] (oracle : ι → K) (ps : List (Program K ι)) :
    Safe oracle (listSum ps) ↔ ∀ p ∈ ps, Safe oracle p := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

@[simp] theorem safe_listProduct [Field K] (oracle : ι → K) (ps : List (Program K ι)) :
    Safe oracle (listProduct ps) ↔ ∀ p ∈ ps, Safe oracle p := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

end Program

end Counting.Algorithm.Interpolation
