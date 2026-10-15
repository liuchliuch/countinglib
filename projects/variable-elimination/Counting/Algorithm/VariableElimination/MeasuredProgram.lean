import Counting.Algorithm.VariableElimination.Program
import Counting.Algorithm.VariableElimination.Cost

/-!
# Arithmetic instrumentation of bucket execution

The instrumented program executes the same scalar joins and sums, materializes
its measured results, and records one arithmetic operation at each loop body.
Factor lookup, scope manipulation, allocation, assignment enumeration, comparisons,
and input callback work are outside this arithmetic-only model. The direct
Horner lookup in `DenseTable.evalIndexed` has separate address instrumentation.
-/

namespace Counting.Algorithm.VariableElimination

variable {V D R : Type} [Fintype V] [LinearOrder V]
variable [Fintype D] [LinearOrder D] [CommSemiring R]

/-- The actual nested scalar loops for a single output row. -/
def measuredBucketRow (v : V) (fs : List (Factor V D R))
    (a : Fin (bucketVars v fs).length → D) : Measured R :=
  Measured.sum ((enumerateValues D).map fun d =>
    Measured.productValues ((bucket v fs).attach.map fun f =>
      f.val.value (bucketRow v fs d a f)))

@[simp] theorem value_measuredBucketRow (v : V) (fs : List (Factor V D R))
    (a : Fin (bucketVars v fs).length → D) :
    (measuredBucketRow v fs a).value = (bucketFactor v fs).value a := by
  simp only [measuredBucketRow, Measured.value_sum, List.map_map,
    Function.comp_def, Measured.value_productValues]
  exact sum_enumerateValues _

@[simp] theorem additions_measuredBucketRow (v : V) (fs : List (Factor V D R))
    (a : Fin (bucketVars v fs).length → D) :
    (measuredBucketRow v fs a).additions = Fintype.card D := by
  simp [measuredBucketRow, Function.comp_def]

@[simp] theorem multiplications_measuredBucketRow (v : V) (fs : List (Factor V D R))
    (a : Fin (bucketVars v fs).length → D) :
    (measuredBucketRow v fs a).multiplications = Fintype.card D * (bucket v fs).length := by
  simp [measuredBucketRow, Function.comp_def]

/-- Materialize the measured row loop exactly once per output assignment. -/
def measuredBucket (v : V) (fs : List (Factor V D R)) :
    Measured (Factor (Remaining v) D R) :=
  let t := DenseTable.tabulateMeasured (measuredBucketRow v fs)
  { value := ⟨(bucketVars v fs).length, (bucketVars v fs).get, t.value.evalIndexed⟩
    additions := t.additions
    multiplications := t.multiplications }

@[simp] theorem value_measuredBucket (v : V) (fs : List (Factor V D R)) :
    (measuredBucket v fs).value = bucketFactor v fs := by
  have h : (DenseTable.tabulateMeasured (measuredBucketRow v fs)).value.evalIndexed =
      (bucketFactor v fs).value := by
    funext a
    simp
  exact congrArg (fun value =>
    (⟨(bucketVars v fs).length, (bucketVars v fs).get, value⟩ : Factor (Remaining v) D R)) h

@[simp] theorem additions_measuredBucket (v : V) (fs : List (Factor V D R)) :
    (measuredBucket v fs).additions =
      Fintype.card D ^ (bucketVars v fs).length * Fintype.card D := by
  simpa only [measuredBucket, Fintype.card_fin] using
    DenseTable.additions_tabulateMeasured_const (measuredBucketRow v fs) (Fintype.card D)
      (additions_measuredBucketRow v fs)

@[simp] theorem multiplications_measuredBucket (v : V) (fs : List (Factor V D R)) :
    (measuredBucket v fs).multiplications =
      Fintype.card D ^ (bucketVars v fs).length *
        (Fintype.card D * (bucket v fs).length) := by
  simpa only [measuredBucket, Fintype.card_fin] using
    DenseTable.multiplications_tabulateMeasured_const (measuredBucketRow v fs)
      (Fintype.card D * (bucket v fs).length) (multiplications_measuredBucketRow v fs)

/-- Instrumented elimination keeps unrelated factors and their tables unchanged. -/
def eliminateMeasured (v : V) (fs : List (Factor V D R)) :
    Measured (List (Factor (Remaining v) D R)) :=
  let b := measuredBucket v fs
  { value := b.value :: retained v fs
    additions := b.additions
    multiplications := b.multiplications }

@[simp] theorem value_eliminateMeasured (v : V) (fs : List (Factor V D R)) :
    (eliminateMeasured v fs).value = eliminate v fs := by
  simp [eliminateMeasured, eliminate]

@[simp] theorem additions_eliminateMeasured (v : V) (fs : List (Factor V D R)) :
    (eliminateMeasured v fs).additions =
      Fintype.card D ^ (bucketVars v fs).length * Fintype.card D :=
  additions_measuredBucket v fs

@[simp] theorem multiplications_eliminateMeasured (v : V) (fs : List (Factor V D R)) :
    (eliminateMeasured v fs).multiplications =
      Fintype.card D ^ (bucketVars v fs).length *
        (Fintype.card D * (bucket v fs).length) :=
  multiplications_measuredBucket v fs

/-- Correctness of the actual measured array-producing step. -/
theorem partition_eliminateMeasured (v : V) (fs : List (Factor V D R)) :
    partition (eliminateMeasured v fs).value = partition fs := by
  rw [value_eliminateMeasured, partition_eliminate]

end Counting.Algorithm.VariableElimination
