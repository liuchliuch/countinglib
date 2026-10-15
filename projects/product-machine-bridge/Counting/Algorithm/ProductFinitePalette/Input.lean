import Counting.Algorithm.Product.Evaluation
import Holant.Proofs.Tractability.ProductFixedField

/-!
# Product occurrences over a fixed coefficient palette

Runtime coefficients are finite palette indices. The actual S1 occurrence list
retains every ordered scope and the explicit variable count. No graph incidence
promise, nonzero premise or injectivity of the coefficient palette is imposed.
-/

namespace Counting.Algorithm.ProductFinitePalette

open Holant.LocalDrafts.Tractability

variable {K : Type} [CommSemiring K] {q n : Nat}

/-- Finite coefficient indices are kept in the syntax, even for equal values. -/
def language (values : Fin q → K) : Model.Language Bool K (Product.Label (Fin q)) where
  arity := Product.Label.arity
  value
    | .scalar c, _ => values c
    | .unary f t, x => if x 0 then values t else values f
    | .equality, x => if x 0 = x 1 then 1 else 0
    | .disequality, x => if x 0 ≠ x 1 then 1 else 0

abbrev Occurrence (values : Fin q → K) (n : Nat) :=
  Model.Occurrence (language values) (Fin n)

/-- Explicit variables include those absent from every occurrence. -/
structure Input (values : Fin q → K) where
  variableCount : Nat
  occurrences : List (Occurrence values variableCount)

variable (values : Fin q → K)

def scalar (c : Fin q) : Occurrence values n := ⟨.scalar c, Fin.elim0⟩
def unary (i : Fin n) (f t : Fin q) : Occurrence values n :=
  ⟨.unary f t, fun _ => i⟩
def equality (i j : Fin n) : Occurrence values n :=
  ⟨.equality, Fin.cons i (Fin.cons j Fin.elim0)⟩
def disequality (i j : Fin n) : Occurrence values n :=
  ⟨.disequality, Fin.cons i (Fin.cons j Fin.elim0)⟩

/-- Interpret indices into the existing public Product language. -/
def publicOccurrence (c : Occurrence values n) : Product.Occurrence K n :=
  match c.symbol, c.scope with
  | .scalar a, _ => Product.scalar (values a)
  | .unary f t, scope => Product.unary (scope (0 : Fin 1)) (values f) (values t)
  | .equality, scope => Product.equality (scope (0 : Fin 2)) (scope (1 : Fin 2))
  | .disequality, scope => Product.disequality (scope (0 : Fin 2)) (scope (1 : Fin 2))

def Input.toPublic (I : Input values) : Product.Instance K :=
  ⟨I.variableCount, I.occurrences.map (publicOccurrence values)⟩

def Input.toOpenInstance (I : Input values) :
    Model.OpenInstance (language values) Empty (Fin I.variableCount) :=
  ⟨I.occurrences.map (fun c => c.rename Sum.inr)⟩

def Input.partition (I : Input values) : K :=
  I.toOpenInstance.partition Empty.elim

@[simp] theorem publicOccurrence_eval (c : Occurrence values n) (x : Fin n → Bool) :
    (publicOccurrence values c).eval x = c.eval x := by
  rcases c with ⟨s, scope⟩
  cases s <;> rfl

theorem Input.toPublic_weight (I : Input values) (x : Fin I.variableCount → Bool) :
    I.toPublic.toOpenInstance.eval Empty.elim x = I.toOpenInstance.eval Empty.elim x := by
  simp [toPublic, Product.Instance.toOpenInstance, toOpenInstance,
    Model.OpenInstance.eval, List.map_map, Function.comp_def]

theorem Input.toPublic_partition (I : Input values) : I.toPublic.partition = I.partition := by
  unfold Product.Instance.partition Input.partition Model.OpenInstance.partition
  apply Finset.sum_congr rfl
  intro x _
  exact I.toPublic_weight values x

/-- One original symbolic factor per occurrence; no contraction or deduplication. -/
def compileOccurrence (c : Occurrence values n) : ProductElimination.LabelledFactor (Fin q) n :=
  match c.symbol, c.scope with
  | .scalar a, _ => .scalar a
  | .unary f t, scope => .unary (scope (0 : Fin 1)) (fun b => if b then t else f)
  | .equality, scope => .link (scope (0 : Fin 2)) (scope (1 : Fin 2)) false
  | .disequality, scope => .link (scope (0 : Fin 2)) (scope (1 : Fin 2)) true

/-- Decode all four factor forms back into their original ordered occurrences. -/
def restoreOccurrence (f : ProductElimination.LabelledFactor (Fin q) n) : Occurrence values n :=
  match f with
  | .scalar a => scalar values a
  | .unary i a => unary values i (a false) (a true)
  | .link i j false => equality values i j
  | .link i j true => disequality values i j

@[simp] theorem restore_compile (c : Occurrence values n) :
    restoreOccurrence values (compileOccurrence values c) = c := by
  rcases c with ⟨s, scope⟩
  cases s with
  | scalar a =>
    dsimp [compileOccurrence, restoreOccurrence, scalar]
    congr 1
    funext i
    exact Fin.elim0 i
  | unary f t =>
    dsimp [compileOccurrence, restoreOccurrence, unary]
    congr 1
    funext i
    fin_cases i
    rfl
  | equality =>
    dsimp [compileOccurrence, restoreOccurrence, equality]
    congr 1
    funext i
    fin_cases i <;> rfl
  | disequality =>
    dsimp [compileOccurrence, restoreOccurrence, disequality]
    congr 1
    funext i
    fin_cases i <;> rfl

@[simp] theorem compile_restore (f : ProductElimination.LabelledFactor (Fin q) n) :
    compileOccurrence values (restoreOccurrence values f) = f := by
  cases f with
  | scalar a => rfl
  | unary i a =>
    dsimp [compileOccurrence, restoreOccurrence, unary]
    congr 1
    funext b
    cases b <;> rfl
  | link i j p => cases p <;> rfl

@[simp] theorem compile_realize (c : Occurrence values n) :
    (compileOccurrence values c).realize values = Product.compileOccurrence (publicOccurrence values c) := by
  rcases c with ⟨s, scope⟩
  cases s with
  | unary f t =>
    dsimp [compileOccurrence, publicOccurrence, Product.compileOccurrence,
      ProductElimination.LabelledFactor.realize, Product.unary]
    congr 1
    funext b
    cases b <;> rfl
  | scalar a => rfl
  | equality => rfl
  | disequality => rfl

/-- The actual original factor-input shape, with all variables retained. -/
def Input.compile (I : Input values) :
    Σ n : Nat, List (ProductElimination.LabelledFactor (Fin q) n) :=
  ⟨I.variableCount, I.occurrences.map (compileOccurrence values)⟩

def restore (x : Σ n : Nat, List (ProductElimination.LabelledFactor (Fin q) n)) : Input values :=
  ⟨x.1, x.2.map (restoreOccurrence values)⟩

@[simp] theorem restore_input (I : Input values) : restore values I.compile = I := by
  cases I
  simp [Input.compile, restore, List.map_map, Function.comp_def]

@[simp] theorem compile_input (x : Σ n : Nat, List (ProductElimination.LabelledFactor (Fin q) n)) :
    (restore values x).compile = x := by
  rcases x with ⟨n, fs⟩
  simp [Input.compile, restore, List.map_map, Function.comp_def]

@[simp] theorem Input.compile_variableCount (I : Input values) : I.compile.1 = I.variableCount := rfl

@[simp] theorem Input.compile_length (I : Input values) :
    I.compile.2.length = I.occurrences.length := by simp [Input.compile]

theorem Input.compile_partition (I : Input values) :
    ProductElimination.partition (I.compile.2.map (ProductElimination.LabelledFactor.realize values)) =
      I.partition := by
  have h : I.compile.2.map (ProductElimination.LabelledFactor.realize values) = I.toPublic.compile := by
    simp [Input.compile, Input.toPublic, Product.Instance.compile, List.map_map,
      Function.comp_def, compile_realize]
  rw [h]
  exact I.toPublic.compile_partition.trans (I.toPublic_partition values)

end Counting.Algorithm.ProductFinitePalette
