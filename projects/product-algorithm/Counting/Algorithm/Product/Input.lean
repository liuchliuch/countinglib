import Counting.Model.Basic

/-!
# Product-type input over the public occurrence semantics

The coefficient type is arbitrary. A label contains at most two coefficients;
its scope is an ordered tuple and may repeat variables. An instance records all
variables explicitly, including those absent from every occurrence.
-/

namespace Counting.Algorithm.Product

/-- The explicit product language: constants, unary tables, and the two Boolean
binary relations. No nonzero restriction is imposed on coefficients. -/
inductive Label (K : Type) where
  | scalar (value : K)
  | unary (onFalse onTrue : K)
  | equality
  | disequality

/-- Ordered arity, including nullary scalar factors. -/
abbrev Label.arity {K : Type} : Label K → Nat
  | .scalar _ => 0
  | .unary _ _ => 1
  | .equality | .disequality => 2

/-- A generic commutative-semiring interpretation of the product language. -/
def language (K : Type) [CommSemiring K] : Model.Language Bool K (Label K) where
  arity := Label.arity
  value
    | .scalar c, _ => c
    | .unary f t, x => if x 0 then t else f
    | .equality, x => if x 0 = x 1 then 1 else 0
    | .disequality, x => if x 0 ≠ x 1 then 1 else 0

abbrev Occurrence (K : Type) [CommSemiring K] (n : Nat) :=
  Model.Occurrence (language K) (Fin n)

/-- A closed product instance. A list retains occurrence multiplicities and the
variable count retains isolated variables. -/
structure Instance (K : Type) [CommSemiring K] where
  variableCount : Nat
  occurrences : List (Occurrence K variableCount)

variable {K : Type} [CommSemiring K] {n : Nat}

/-- Convenience constructors retain the given port order and repeated ports. -/
def scalar (c : K) : Occurrence K n := ⟨.scalar c, Fin.elim0⟩
def unary (i : Fin n) (onFalse onTrue : K) : Occurrence K n :=
  ⟨.unary onFalse onTrue, fun _ => i⟩
def equality (i j : Fin n) : Occurrence K n :=
  ⟨.equality, Fin.cons i (Fin.cons j Fin.elim0)⟩
def disequality (i j : Fin n) : Occurrence K n :=
  ⟨.disequality, Fin.cons i (Fin.cons j Fin.elim0)⟩

/-- The original occurrence list, with every variable hidden and no boundary. -/
def Instance.toOpenInstance (I : Instance K) :
    Model.OpenInstance (language K) Empty (Fin I.variableCount) :=
  ⟨I.occurrences.map (fun c => c.rename Sum.inr)⟩

/-- The public S1 sum-product value, not an algorithm specification field. -/
def Instance.partition (I : Instance K) : K :=
  I.toOpenInstance.partition Empty.elim

/-- Every occurrence counts, including repeated and nullary ones. -/
def Instance.factorCount (I : Instance K) : Nat := I.occurrences.length

@[simp] theorem Instance.occurrence_count (I : Instance K) :
    I.toOpenInstance.occurrences.length = I.factorCount := by
  simp [toOpenInstance, factorCount]

end Counting.Algorithm.Product
