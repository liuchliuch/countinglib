import Counting.Algorithm.VariableElimination.Model

namespace Counting.Algorithm.VariableElimination

variable {V D R : Type} [Fintype V] [LinearOrder V]

/-- The bucket contains exactly the incident occurrences, in their original order. -/
def bucket (v : V) (fs : List (Factor V D R)) : List (Factor V D R) :=
  fs.filter fun f => v ∈ f.support

/-- Unrelated occurrences are retained, with multiplicities and order. -/
def outside (v : V) (fs : List (Factor V D R)) : List (Factor V D R) :=
  fs.filter fun f => v ∉ f.support

/-- Variables appearing in any occurrence in a list. -/
def support (fs : List (Factor V D R)) : Finset V :=
  (fs.map Factor.support).foldr (· ∪ ·) ∅

omit [Fintype V] in
@[simp] theorem mem_support (fs : List (Factor V D R)) (v : V) :
    v ∈ support fs ↔ ∃ f ∈ fs, v ∈ f.support := by
  induction fs with
  | nil => simp [support]
  | cons f fs ih =>
    change v ∈ f.support ∪ support fs ↔ _
    simp only [Finset.mem_union, ih, List.mem_cons, exists_eq_or_imp]

/-- The dynamically induced scope, excluding the eliminated variable. -/
def bucketVars (v : V) (fs : List (Factor V D R)) : List (Remaining v) :=
  (Finset.univ.filter fun w : Remaining v => w.val ∈ support (bucket v fs)).sort (· ≤ ·)

@[simp] theorem mem_bucketVars (v : V) (fs : List (Factor V D R)) (w : Remaining v) :
    w ∈ bucketVars v fs ↔ w.val ∈ support (bucket v fs) := by
  simp [bucketVars]

/-- Read an entry of a scoped row by its variable, using the canonical scope order. -/
def readRow (v : V) (fs : List (Factor V D R)) (a : Fin (bucketVars v fs).length → D)
    (w : Remaining v) (h : w.val ∈ support (bucket v fs)) : D :=
  a ⟨(bucketVars v fs).idxOf w, List.idxOf_lt_length_iff.mpr ((mem_bucketVars v fs w).mpr h)⟩

def bucketRow (v : V) (fs : List (Factor V D R)) (d : D)
    (a : Fin (bucketVars v fs).length → D) (f : {f // f ∈ bucket v fs}) :
    Fin f.val.arity → D := fun i =>
  if h : f.val.scope i = v then d
  else readRow v fs a ⟨f.val.scope i, h⟩
    ((mem_support _ _).mpr ⟨f.val, f.property, (Factor.mem_support _ _).mpr ⟨i, rfl⟩⟩)

/-- Mathematical specification of the new table: join the incident bucket and sum
only the pivot value. Other factors do not occur in this expression. -/
def bucketFactor [CommSemiring R] [Fintype D] (v : V) (fs : List (Factor V D R)) :
    Factor (Remaining v) D R where
  arity := (bucketVars v fs).length
  scope := (bucketVars v fs).get
  value := fun a => ∑ d : D,
    ((bucket v fs).attach.map fun f => f.val.value (bucketRow v fs d a f)).prod

/-- Change only the variable names of an unrelated factor; its value table is reused. -/
def retain (v : V) (f : Factor V D R) (h : v ∉ f.support) : Factor (Remaining v) D R where
  arity := f.arity
  scope := fun i => ⟨f.scope i, fun hi => h ((Factor.mem_support _ _).mpr ⟨i, hi⟩)⟩
  value := f.value

omit [Fintype V] in
@[simp] theorem eval_retain (v : V) (f : Factor V D R) (h : v ∉ f.support)
    (d : D) (a : Remaining v → D) : (retain v f h).eval a = f.eval (extend v d a) := by
  unfold Factor.eval retain
  congr 1
  funext i
  simp only [Function.comp_apply]
  simp only [extend]
  split_ifs with hi
  · exact False.elim (h ((Factor.mem_support _ _).mpr ⟨i, hi⟩))
  · rfl

def retained (v : V) (fs : List (Factor V D R)) : List (Factor (Remaining v) D R) :=
  (outside v fs).attach.map fun f => retain v f.val (by
    have hf := List.mem_filter.mp f.property
    simpa using hf.2)

@[simp] theorem readRow_scope (v : V) (fs : List (Factor V D R)) (a : Remaining v → D)
    (w : Remaining v) (h : w.val ∈ support (bucket v fs)) :
    readRow v fs (a ∘ (bucketVars v fs).get) w h = a w := by
  simp [readRow, List.get_eq_getElem, List.getElem_idxOf]

@[simp] theorem bucketRow_scope (v : V) (fs : List (Factor V D R))
    (d : D) (a : Remaining v → D) (f : {f // f ∈ bucket v fs}) :
    bucketRow v fs d (a ∘ (bucketVars v fs).get) f = extend v d a ∘ f.val.scope := by
  funext i
  simp only [bucketRow, Function.comp_apply, extend]
  split_ifs with h
  · rfl
  · exact readRow_scope v fs a _ _

theorem eval_bucketFactor [CommSemiring R] [Fintype D] (v : V)
    (fs : List (Factor V D R)) (a : Remaining v → D) :
    (bucketFactor v fs).eval a = ∑ d : D, weight (bucket v fs) (extend v d a) := by
  unfold Factor.eval bucketFactor
  simp only [bucketRow_scope]
  simp [weight, Factor.eval]

omit [Fintype V] in
theorem weight_retained [CommMonoid R] (v : V) (fs : List (Factor V D R))
    (d : D) (a : Remaining v → D) :
    weight (retained v fs) a = weight (outside v fs) (extend v d a) := by
  simp [weight, retained, eval_retain v _ _ d a]

omit [Fintype V] in
theorem weight_split [CommMonoid R] (v : V) (fs : List (Factor V D R)) (a : V → D) :
    weight fs a = weight (bucket v fs) a * weight (outside v fs) a := by
  induction fs with
  | nil => simp [weight, bucket, outside]
  | cons f fs ih =>
    by_cases h : v ∈ f.support
    · simpa only [weight, bucket, outside, List.filter_cons, h, not_true_eq_false,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        List.prod_cons, mul_assoc] using congrArg (f.eval a * ·) ih
    · simpa only [weight, bucket, outside, List.filter_cons, h, not_false_eq_true,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        List.prod_cons, mul_assoc, mul_left_comm, mul_comm] using congrArg (f.eval a * ·) ih

/-- A pointwise invariant: after one step the remaining assignment has exactly
its former marginal weight. -/
theorem weight_bucket_elimination [CommSemiring R] [Fintype D] (v : V)
    (fs : List (Factor V D R)) (a : Remaining v → D) :
    weight (bucketFactor v fs :: retained v fs) a = ∑ d : D, weight fs (extend v d a) := by
  change (bucketFactor v fs).eval a * weight (retained v fs) a = _
  rw [eval_bucketFactor, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [weight_retained v fs d a, ← weight_split]

/-- One bucket step preserves the finite partition, including empty domains. -/
theorem partition_bucket_elimination [CommSemiring R] [Fintype D] (v : V)
    (fs : List (Factor V D R)) :
    partition (bucketFactor v fs :: retained v fs) = partition fs := by
  unfold partition
  simp_rw [weight_bucket_elimination]
  exact (sum_extend v (weight fs)).symm

end Counting.Algorithm.VariableElimination
