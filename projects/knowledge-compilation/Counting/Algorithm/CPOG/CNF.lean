import Counting.Model.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Ordered CNF occurrences as public partition instances. Clauses and literals
remain lists; variable types include every declared variable, including isolated
ones. The weighted construction appends one explicit unary factor per variable. -/
namespace Counting.Algorithm.CPOG.CNF
open scoped BigOperators
open Counting.Model

structure Literal (n : ℕ) where
  index : Fin n
  positive : Bool
  deriving DecidableEq, Repr

namespace Literal
def apply {n : ℕ} (l : Literal n) (b : Bool) : Bool := if l.positive then b else !b
def eval {n : ℕ} (l : Literal n) (a : Fin n → Bool) : Bool := l.apply (a l.index)
end Literal

abbrev Clause (n : ℕ) := List (Literal n)
abbrev Formula (n : ℕ) := List (Clause n)

namespace Clause
def eval {n : ℕ} (C : Clause n) (a : Fin n → Bool) : Bool := C.any (fun l => l.eval a)

/-- Each occurrence position, rather than a set of variables, is one table port. -/
def portEval {n : ℕ} (C : Clause n) (xs : Fin C.length → Bool) : Bool :=
  (List.ofFn (fun j => (C.get j).apply (xs j))).any id

theorem portEval_assignment {n : ℕ} (C : Clause n) (a : Fin n → Bool) :
    C.portEval (fun j => a (C.get j).index) = C.eval a := by
  change (List.ofFn (fun j => (C.get j).eval a)).any id = C.any (fun l => l.eval a)
  have h : List.ofFn (fun j => (C.get j).eval a) = C.map (fun l => l.eval a) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map (fun l : Literal n => l.eval a)) (List.ofFn_get C)
  rw [h, List.any_map]
  rfl

@[simp] theorem eval_nil {n : ℕ} (a : Fin n → Bool) : Clause.eval ([] : Clause n) a = false := rfl

@[simp] theorem eval_cons {n : ℕ} (l : Literal n) (C : Clause n) (a : Fin n → Bool) :
    Clause.eval (l :: C) a = (l.eval a || C.eval a) := rfl
end Clause

namespace Formula
variable {n : ℕ}

def eval (F : Formula n) (a : Fin n → Bool) : Bool := F.all (fun C => C.eval a)

@[simp] theorem eval_nil (a : Fin n → Bool) : Formula.eval ([] : Formula n) a = true := rfl
@[simp] theorem eval_cons (C : Clause n) (F : Formula n) (a : Fin n → Bool) :
    Formula.eval (C :: F) a = (C.eval a && F.eval a) := rfl

/-- Labels are clause occurrence indices, retaining repeated clauses. -/
def language (R : Type) [Zero R] [One R] (F : Formula n) : Language Bool R (Fin F.length) where
  arity i := (F.get i).length
  value i xs := if (F.get i).portEval xs then 1 else 0

def occurrence (R : Type) [Zero R] [One R] (F : Formula n) (i : Fin F.length) :
    Occurrence (F.language R) (Empty ⊕ Fin n) where
  symbol := i
  scope j := Sum.inr ((F.get i).get j).index

theorem occurrence_scope (R : Type) [Zero R] [One R] (F : Formula n)
    (i : Fin F.length) (j : Fin (F.get i).length) :
    (F.occurrence R i).scope j = Sum.inr ((F.get i).get j).index := rfl

theorem occurrence_eval (R : Type) [Zero R] [One R] (F : Formula n)
    (i : Fin F.length) (a : Fin n → Bool) :
    (F.occurrence R i).eval (Sum.elim Empty.elim a) = if (F.get i).eval a then 1 else 0 := by
  change (if (F.get i).portEval (fun j => a ((F.get i).get j).index) then 1 else 0) = _
  rw [Clause.portEval_assignment]

def toInstance (F : Formula n) : OpenInstance (F.language ℕ) Empty (Fin n) where
  occurrences := List.ofFn (F.occurrence ℕ)

theorem occurrences_length (F : Formula n) : (F.toInstance).occurrences.length = F.length := by
  change (List.ofFn (F.occurrence ℕ)).length = _
  exact List.length_ofFn

theorem indicator_product {R : Type} [CommSemiring R] (F : Formula n) (a : Fin n → Bool) :
    (F.map (fun C => if C.eval a then (1 : R) else 0)).prod = if F.eval a then 1 else 0 := by
  induction F with
  | nil => simp
  | cons C F ih =>
    simp only [List.map_cons, List.prod_cons, eval_cons, ih]
    by_cases hc : C.eval a = true <;> by_cases hf : Formula.eval F a = true <;>
      simp [Bool.and_eq_true, hc, hf]

theorem indexed_indicator_product {R : Type} [CommSemiring R] (F : Formula n)
    (a : Fin n → Bool) :
    (∏ i : Fin F.length, if (F.get i).eval a then (1 : R) else 0) = if F.eval a then 1 else 0 := by
  rw [← List.prod_ofFn]
  have h : List.ofFn (fun i => if (F.get i).eval a then (1 : R) else 0) =
      F.map (fun C => if C.eval a then 1 else 0) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map (fun C : Clause n => if C.eval a then (1 : R) else 0)) (List.ofFn_get F)
  rw [h, indicator_product]

theorem eval_toInstance (F : Formula n) (a : Fin n → Bool) :
    F.toInstance.eval Empty.elim a = if F.eval a then 1 else 0 := by
  change ((List.ofFn (F.occurrence ℕ)).map (fun c => c.eval (Sum.elim Empty.elim a))).prod = _
  simp only [List.map_ofFn, Function.comp_def, occurrence_eval, List.prod_ofFn]
  exact indexed_indicator_product F a

theorem partition_eq_sum (F : Formula n) :
    F.toInstance.partition Empty.elim = ∑ a : Fin n → Bool, if F.eval a then 1 else 0 := by
  change (∑ a : Fin n → Bool, F.toInstance.eval Empty.elim a) = _
  exact Finset.sum_congr rfl (fun a _ => eval_toInstance F a)

/-- Every variable, even an isolated one, is an explicitly represented unary label. -/
def weightedLanguage {R : Type} [CommRing R] (F : Formula n) (w : Fin n → R) :
    Language Bool R (Fin F.length ⊕ Fin n) where
  arity | .inl i => (F.get i).length | .inr _ => 1
  value
    | .inl i, xs => if (F.get i).portEval xs then 1 else 0
    | .inr i, xs => if xs 0 then w i else 1 - w i

def weightedClauseOccurrence {R : Type} [CommRing R] (F : Formula n) (w : Fin n → R)
    (i : Fin F.length) : Occurrence (F.weightedLanguage w) (Empty ⊕ Fin n) where
  symbol := .inl i
  scope j := Sum.inr ((F.get i).get j).index

def weightedVariableOccurrence {R : Type} [CommRing R] (F : Formula n) (w : Fin n → R)
    (i : Fin n) : Occurrence (F.weightedLanguage w) (Empty ⊕ Fin n) where
  symbol := .inr i
  scope _ := Sum.inr i

def weightedInstance {R : Type} [CommRing R] (F : Formula n) (w : Fin n → R) :
    OpenInstance (F.weightedLanguage w) Empty (Fin n) where
  occurrences := List.ofFn (F.weightedClauseOccurrence w) ++ List.ofFn (F.weightedVariableOccurrence w)

theorem weighted_occurrences_length {R : Type} [CommRing R] (F : Formula n) (w : Fin n → R) :
    (F.weightedInstance w).occurrences.length = F.length + n := by
  change (List.ofFn (F.weightedClauseOccurrence w) ++ List.ofFn (F.weightedVariableOccurrence w)).length = _
  simp

theorem weightedClauseOccurrence_eval {R : Type} [CommRing R] (F : Formula n)
    (w : Fin n → R) (i : Fin F.length) (a : Fin n → Bool) :
    (F.weightedClauseOccurrence w i).eval (Sum.elim Empty.elim a) =
      if (F.get i).eval a then 1 else 0 := by
  change (if (F.get i).portEval (fun j => a ((F.get i).get j).index) then 1 else 0) = _
  rw [Clause.portEval_assignment]

theorem weightedVariableOccurrence_eval {R : Type} [CommRing R] (F : Formula n)
    (w : Fin n → R) (i : Fin n) (a : Fin n → Bool) :
    (F.weightedVariableOccurrence w i).eval (Sum.elim Empty.elim a) =
      if a i then w i else 1 - w i := rfl

theorem eval_weightedInstance {R : Type} [CommRing R] (F : Formula n)
    (w : Fin n → R) (a : Fin n → Bool) :
    (F.weightedInstance w).eval Empty.elim a =
      if F.eval a then (∏ i, if a i then w i else 1 - w i) else 0 := by
  change (((List.ofFn (F.weightedClauseOccurrence w) ++ List.ofFn (F.weightedVariableOccurrence w)).map
    (fun c => c.eval (Sum.elim Empty.elim a))).prod) = _
  simp only [List.map_append, List.prod_append, List.map_ofFn, Function.comp_def,
    weightedClauseOccurrence_eval, weightedVariableOccurrence_eval, List.prod_ofFn]
  rw [indexed_indicator_product]
  by_cases hf : Formula.eval F a = true <;> simp [hf]

theorem weighted_partition_eq_sum {R : Type} [CommRing R] (F : Formula n) (w : Fin n → R) :
    (F.weightedInstance w).partition Empty.elim =
      ∑ a : Fin n → Bool, if F.eval a then (∏ i, if a i then w i else 1 - w i) else 0 := by
  change (∑ a : Fin n → Bool, (F.weightedInstance w).eval Empty.elim a) = _
  exact Finset.sum_congr rfl (fun a _ => eval_weightedInstance F w a)

theorem partition_empty : (toInstance ([] : Formula n)).partition Empty.elim = 2^n := by
  rw [partition_eq_sum]
  simp

theorem partition_empty_clause (F : Formula n) :
    (toInstance (([] : Clause n) :: F)).partition Empty.elim = 0 := by
  rw [partition_eq_sum]
  simp

theorem weighted_partition_empty {R : Type} [CommRing R] (w : Fin n → R) :
    (weightedInstance ([] : Formula n) w).partition Empty.elim = 1 := by
  rw [weighted_partition_eq_sum]
  simp only [eval_nil, ↓reduceIte]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => if b then w i else 1 - w i)]
  apply Finset.prod_eq_one
  intro i _
  simp [Fintype.sum_bool, add_comm]

theorem weighted_partition_empty_clause {R : Type} [CommRing R] (F : Formula n) (w : Fin n → R) :
    (weightedInstance (([] : Clause n) :: F) w).partition Empty.elim = 0 := by
  rw [weighted_partition_eq_sum]
  simp

end Formula
end Counting.Algorithm.CPOG.CNF
