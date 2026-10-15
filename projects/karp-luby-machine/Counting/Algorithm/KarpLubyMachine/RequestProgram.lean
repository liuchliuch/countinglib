import Counting.Algorithm.KarpLubyMachine.DenseNormalization
import Counting.Algorithm.KarpLubyMachine.NumeratorMedian
import Counting.Algorithm.KarpLuby.Guarantee
import Counting.Algorithm.KarpLuby.EncodedBounds

/-!
# A materialized structured-request evaluator

The program allocates dense clauses once, computes the sample/group/word budgets,
validates the exact tape length, and runs the original estimator on the interpreted
tables. Every finite Boolean tape has the same result as R1's request evaluator.

The instrumented model charges list cells, Boolean tests, and arithmetic/access
operations. In particular rational comparisons, natural division/multiplication,
and interpreted table/vector access are still primitives. This is a complete
cost for the *structured* request in that explicitly intermediate model, not a
bit-time theorem. Parsing raw request bits and serializing the final rational are
separate endpoints and are not hidden in the claimed cost.
-/
namespace Counting.Algorithm.KarpLubyMachine.RequestProgram

open Counting.Algorithm.KarpLuby
open DNF Cost

/-- The length loop charges the terminating inspection as well as every cell. -/
def length {α : Type} : List α → Evaluation ℕ
  | [] => ⟨0, 1⟩
  | _ :: xs => let r := length xs; ⟨r.value + 1, r.operations + 1⟩

@[simp] theorem length_value {α : Type} (xs : List α) : (length xs).value = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [length, ih]

@[simp] theorem length_operations {α : Type} (xs : List α) :
    (length xs).operations = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [length, ih]

/-- Numerator-to-natural, division, and increment are three arithmetic primitives. -/
def reciprocal (q : ℚ) : Evaluation ℕ := ⟨q.den / q.num.toNat + 1, 3⟩

@[simp] theorem reciprocal_value (q : ℚ) : (reciprocal q).value = reciprocalCeiling q := rfl

/-- Squaring is two ordinary multiplications after multiplication by the term count. -/
def sampleCount (m : ℕ) (q : ℚ) : Evaluation ℕ :=
  let r := reciprocal q
  ⟨144 * m * r.value * r.value, r.operations + 3⟩

@[simp] theorem sampleCount_value (m : ℕ) (q : ℚ) :
    (sampleCount m q).value = samples m q := by simp [sampleCount, samples, pow_two, Nat.mul_assoc]

@[simp] theorem sampleCount_operations (m : ℕ) (q : ℚ) :
    (sampleCount m q).operations = 6 := rfl

/-- Confidence size uses the actual binary-recursive bit-length loop from R1. -/
def groupCount (q : ℚ) : Evaluation ℕ :=
  let r := reciprocal q
  let width := Cost.bitLength r.value
  ⟨2 * (width.value + 1), r.operations + width.operations + 2⟩

@[simp] theorem groupCount_value (q : ℚ) :
    (groupCount q).value = Program.requestedGroups q := by
  simp [groupCount, Program.requestedGroups, confidenceGroups]

@[simp] theorem groupCount_operations (q : ℚ) :
    (groupCount q).operations = 5 * (reciprocalCeiling q).size + 6 := by
  simp [groupCount, reciprocal, reciprocalCeiling]; omega

/-- Build each semantic lookup closure once, charging the list traversal and
construction. The closure refers to a dense table, never an update chain. -/
def interpret (n : ℕ) : List DenseNormalization.Cells → Evaluation (List (Clause n))
  | [] => ⟨[], 1⟩
  | xs :: rest =>
    let r := interpret n rest
    ⟨DenseNormalization.denote n xs :: r.value, r.operations + 2⟩

@[simp] theorem interpret_value (n : ℕ) (tables : List DenseNormalization.Cells) :
    (interpret n tables).value = tables.map (DenseNormalization.denote n) := by
  induction tables with
  | nil => rfl
  | cons xs rest ih => simp [interpret, ih]

@[simp] theorem interpret_operations (n : ℕ) (tables : List DenseNormalization.Cells) :
    (interpret n tables).operations = 2 * tables.length + 1 := by
  induction tables with
  | nil => rfl
  | cons xs rest ih => simp [interpret, ih]; omega

/-- Fully materialized clauses and the three numerical loop dimensions. -/
structure Prepared (n : ℕ) where
  tables : List DenseNormalization.Cells
  clauses : List (Clause n)
  sampleCount : ℕ
  groupCount : ℕ
  wordWidth : ℕ

def Prepared.budget {n : ℕ} (p : Prepared n) : ℕ :=
  p.groupCount * (p.sampleCount * p.wordWidth)

/-- Normalize only once. The mass/width scan is included even on a later
wrong-length rejection, as required to decide the exact tape contract. -/
def prepare {n : ℕ} (f : Formula n) (epsilon delta : ℚ) : Evaluation (Prepared n) :=
  let tables := DenseNormalization.formula n f
  let viewed := interpret n tables.value
  let count := length tables.value
  let samples := sampleCount count.value epsilon
  let groups := groupCount delta
  let mass := Cost.totalMass viewed.value
  let width := Cost.bitLength mass.value
  ⟨⟨tables.value, viewed.value, samples.value, groups.value, width.value⟩,
    tables.operations + viewed.operations + count.operations + samples.operations + groups.operations +
      mass.operations + width.operations + 2⟩

@[simp] theorem prepare_tables {n : ℕ} (f : Formula n) (epsilon delta : ℚ) :
    (prepare f epsilon delta).value.tables = (DenseNormalization.formula n f).value := rfl

@[simp] theorem prepare_clauses {n : ℕ} (f : Formula n) (epsilon delta : ℚ) :
    (prepare f epsilon delta).value.clauses = normalizeFormula f := by
  simp [prepare]

@[simp] theorem prepare_samples {n : ℕ} (f : Formula n) (epsilon delta : ℚ) :
    (prepare f epsilon delta).value.sampleCount =
      Program.requestedSamples (normalizeFormula f) epsilon := by
  have hl := congrArg List.length (DenseNormalization.formula_refines f)
  simp only [List.length_map] at hl
  simp [prepare, Program.requestedSamples, hl]

@[simp] theorem prepare_groups {n : ℕ} (f : Formula n) (epsilon delta : ℚ) :
    (prepare f epsilon delta).value.groupCount = Program.requestedGroups delta := by simp [prepare]

@[simp] theorem prepare_width {n : ℕ} (f : Formula n) (epsilon delta : ℚ) :
    (prepare f epsilon delta).value.wordWidth =
      dyadicBits (Program.totalMass (normalizeFormula f)) := by simp [prepare, dyadicBits]

@[simp] theorem prepare_budget {n : ℕ} (f : Formula n) (epsilon delta : ℚ) :
    (prepare f epsilon delta).value.budget = Program.requestedBudget f epsilon delta := by
  simp [Prepared.budget, Program.requestedBudget, Program.randomBitBudget]

/-- Exact accounting identity for every executed preprocessing stage. -/
theorem prepare_operations {n : ℕ} (f : Formula n) (epsilon delta : ℚ) :
    (prepare f epsilon delta).operations =
      (DenseNormalization.formula n f).operations + (2 * (normalizeFormula f).length + 1) +
      (normalizeFormula f).length + 1 + 6 +
      (5 * (reciprocalCeiling delta).size + 6) +
      (Cost.totalMass (normalizeFormula f)).operations +
      (5 * (Program.totalMass (normalizeFormula f)).size + 1) + 2 := by
  have hl := congrArg List.length (DenseNormalization.formula_refines f)
  simp only [List.length_map] at hl
  simp [prepare, hl]; omega

/-- The whole materialized preparation has an explicit polynomial operation bound. -/
theorem prepare_operations_le {n : ℕ} (f : Formula n) (epsilon delta : ℚ) :
    (prepare f epsilon delta).operations ≤
      1 + f.length * (n + 4) + (f.map List.length).sum * (2 * n + 4) +
      (2 * f.length + 1) + f.length + 1 + 6 + (5 * (delta.den.size + 1) + 6) +
      f.length * (3 * n + 1) + 5 * (f.length + n + 1) + 1 + 2 := by
  have hn := DenseNormalization.formula_operations_le f
  have hl := ResourceBounds.normalized_length_le f
  have hm := Cost.totalMass_operations_le (normalizeFormula f)
  have hb := Cost.totalMass_size_le (normalizeFormula f)
  have hs : (normalizeFormula f).length.size ≤ f.length :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans hl
  have hd : (reciprocalCeiling delta).size ≤ delta.den.size + 1 := by
    apply (Nat.size_le_size (reciprocalCeiling_le_den_add_one delta)).trans
    apply Nat.size_le.mpr
    have h := Nat.lt_size_self delta.den
    rw [pow_succ]
    omega
  rw [prepare_operations]
  have hmass : (Cost.totalMass (normalizeFormula f)).operations ≤ f.length * (3 * n + 1) :=
    hm.trans (Nat.mul_le_mul_right _ hl)
  omega

/-- The explicit polynomial bound inherited by the full median of group means. -/
def estimatorBound (n m s g : ℕ) : ℕ :=
  g * (s * ((m + n + 1) * (m + n + 5) + m * (15 * n + 6) +
    6 * (m + n + 1) + 5) + 2) + 2 * g + g * (3 * g + 4) + 3

/-- Total list-backed tape access; the request validator separately proves that
all accessed positions lie inside the supplied finite tape. -/
def estimateFromList {n : ℕ} (cs : List (Clause n)) (s g width : ℕ)
    (raw : List Bool) : Evaluation ℚ :=
  let selected := NumeratorMedian.estimateWithWidth cs s g width
    (fun i => raw[i.val]?.getD false)
  ⟨(selected.value : ℚ) / s, selected.operations + 1⟩

/-- The supplied width is the one computed by preparation. The bound includes
both the group-slice multiplication and the single final rational division. -/
theorem estimateFromList_operations_le {n : ℕ} (cs : List (Clause n)) (s g width : ℕ)
    (raw : List Bool) (hw : width ≤ cs.length + n + 1) :
    (estimateFromList cs s g width raw).operations ≤ estimatorBound n cs.length s g := by
  have he := NumeratorMedian.estimateWithWidth_operations_le cs s g width
    (fun i => raw[i.val]?.getD false)
  have hmul : width * (width + 4) ≤ (cs.length + n + 1) * (cs.length + n + 5) :=
    Nat.mul_le_mul hw (by omega)
  have hmono : g * (s * (width * (width + 4) + NumeratorMedian.trialBound n cs.length + 1) + 2) ≤
      g * (s * ((cs.length + n + 1) * (cs.length + n + 5) +
        NumeratorMedian.trialBound n cs.length + 1) + 2) := by gcongr
  simp only [estimateFromList]
  calc
    _ ≤ (g * (s * (width * (width + 4) + NumeratorMedian.trialBound n cs.length + 1) + 2) +
      2 * g + g * (3 * g + 4) + 2) + 1 := Nat.add_le_add_right he 1
    _ ≤ estimatorBound n cs.length s g := by
      unfold estimatorBound NumeratorMedian.trialBound at *
      nlinarith [hmono]

/-- A total structured request evaluator, including invalid-parameter and
wrong-length branches. Dense tables are constructed once and shared. -/
def evalRequest (r : ProgramEncoding.Request) : Evaluation ℚ :=
  if Program.ValidRequest r.epsilon r.delta then
    let p := prepare r.problem.formula r.epsilon r.delta
    let len := length r.tape
    if len.value = p.value.budget then
      let result := estimateFromList p.value.clauses p.value.sampleCount p.value.groupCount p.value.wordWidth r.tape
      ⟨result.value, p.operations + len.operations + result.operations + 8⟩
    else ⟨0, p.operations + len.operations + 8⟩
  else ⟨0, 7⟩

/-- Same result for every structured request, including all rejection branches. -/
@[simp] theorem evalRequest_value (r : ProgramEncoding.Request) :
    (evalRequest r).value = ProgramEncoding.evalRequest r := by
  simp only [evalRequest, length_value, prepare_budget, prepare_clauses,
    prepare_samples, prepare_groups, prepare_width, ProgramEncoding.evalRequest]
  split_ifs with hv hl
  · have hm := NumeratorMedian.estimateWithWidth_refines (normalizeFormula r.problem.formula)
      (Program.requestedSamples (normalizeFormula r.problem.formula) r.epsilon)
      (Program.requestedGroups r.delta) (fun i => r.tape[i.val]?.getD false)
    apply hm.symm.trans
    simp only [Program.run]
    congr 1
    funext i
    have hi : i.val < r.tape.length := by rw [hl]; exact i.isLt
    simp [List.getElem?_eq_getElem hi]
  · rfl
  · rfl

/-- Complete structured-request operation count, bounded uniformly over its
finite tape contents. This includes normalization and request adapters. -/
theorem evalRequest_operations_le (r : ProgramEncoding.Request) :
    (evalRequest r).operations ≤
      (prepare r.problem.formula r.epsilon r.delta).operations + r.tape.length + 1 +
      estimatorBound r.problem.variableCount (normalizeFormula r.problem.formula).length
        (Program.requestedSamples (normalizeFormula r.problem.formula) r.epsilon)
        (Program.requestedGroups r.delta) + 8 := by
  have hw : (prepare r.problem.formula r.epsilon r.delta).value.wordWidth ≤
      (prepare r.problem.formula r.epsilon r.delta).value.clauses.length +
        r.problem.variableCount + 1 := by
    simp only [prepare_clauses, prepare_width, dyadicBits]
    have hm := Cost.totalMass_size_le (normalizeFormula r.problem.formula)
    have hl : (normalizeFormula r.problem.formula).length.size ≤
        (normalizeFormula r.problem.formula).length := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have he := estimateFromList_operations_le
    (prepare r.problem.formula r.epsilon r.delta).value.clauses
    (prepare r.problem.formula r.epsilon r.delta).value.sampleCount
    (prepare r.problem.formula r.epsilon r.delta).value.groupCount
    (prepare r.problem.formula r.epsilon r.delta).value.wordWidth r.tape hw
  simp only [prepare_clauses, prepare_samples, prepare_groups] at he
  unfold evalRequest
  split_ifs
  · dsimp only
    split_ifs <;> simp only [length_operations, prepare_clauses, prepare_samples, prepare_groups] <;> omega
  · dsimp only; omega

/-- Explicit-variable, fixed-tape semantics survives the materialized frontend. -/
theorem evalRequest_ofRun {n : ℕ} (f : Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    (evalRequest (ProgramEncoding.ofRun f epsilon delta tape)).value =
      Program.run f epsilon delta tape := by
  rw [evalRequest_value, ProgramEncoding.evalRequest_ofRun f epsilon delta hvalid tape]

/-- Exact zero holds for every tape, including formulas with unused variables. -/
theorem evalRequest_zero {n : ℕ} (f : Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta) (hz : modelCount f = 0)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    (evalRequest (ProgramEncoding.ofRun f epsilon delta tape)).value = 0 := by
  rw [evalRequest_ofRun f epsilon delta hvalid tape]
  exact Program.run_zero f epsilon delta hz tape

/-- PAC is transported only along the proved value equality; no time claim is added. -/
theorem evalRequest_success {n : ℕ} (f : Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta) :
    1 - delta ≤ HiddenCircuits.Approximation.SelfReduction.probability
      (fun tape : CoinTape (Program.requestedBudget f epsilon delta) =>
        |(evalRequest (ProgramEncoding.ofRun f epsilon delta tape)).value - modelCount f| ≤
          epsilon * modelCount f) := by
  simpa only [evalRequest_ofRun f epsilon delta hvalid] using
    Program.run_success f epsilon delta hvalid.1 hvalid.2.2.1

end Counting.Algorithm.KarpLubyMachine.RequestProgram
