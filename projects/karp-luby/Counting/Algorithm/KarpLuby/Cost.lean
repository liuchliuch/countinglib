import Counting.Algorithm.KarpLuby.Program
import Mathlib.Data.Nat.Size

/-!
# Structural operation counts and encoded magnitude bounds

These instrumented evaluators return both their ordinary value and an operation
count. The projection theorems relate them to the production functions. Costs
are derived from executed recursive branches rather than attached to outputs.
Clause/assignment coordinate access and natural arithmetic are unit operations
in this intermediate model; it is explicitly not a TM2 bit-time theorem.
-/
namespace Counting.Algorithm.KarpLuby.Cost

open DNF

/-- A value together with the cost accumulated by its recursive computation. -/
structure Evaluation (α : Type) where
  value : α
  operations : ℕ

/-- Instrumented clause scan. Each coordinate examination costs one operation;
checking a fixed Boolean and combining results each cost one further operation.
This conservative scan evaluates the tail even after a failed fixed literal. -/
def evalClause : {n : ℕ} → Clause n → Assignment n → Evaluation Bool
  | 0, _, _ => ⟨true, 0⟩
  | _ + 1, c, a =>
    let tail := evalClause (fun i => c i.succ) (fun i => a i.succ)
    match c 0 with
    | none => ⟨tail.value, tail.operations + 1⟩
    | some b => ⟨(a 0 == b) && tail.value, tail.operations + 3⟩

@[simp] theorem evalClause_value {n : ℕ} (c : Clause n) (a : Assignment n) :
    (evalClause c a).value = DNF.evalClause c a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [evalClause, DNF.evalClause]
    cases c 0 <;> simp [ih]

/-- The actual recursive instrumented scan performs at most `3n` operations. -/
theorem evalClause_operations_le {n : ℕ} (c : Clause n) (a : Assignment n) :
    (evalClause c a).operations ≤ 3 * n := by
  induction n with
  | zero => simp [evalClause]
  | succ n ih =>
    have h := ih (fun i => c i.succ) (fun i => a i.succ)
    simp only [evalClause]
    cases c 0 <;> simp only <;> omega

/-- Instrumented free-coordinate scan. -/
def freeCount : {n : ℕ} → Clause n → Evaluation ℕ
  | 0, _ => ⟨0, 0⟩
  | _ + 1, c =>
    let tail := freeCount (fun i => c i.succ)
    match c 0 with
    | none => ⟨tail.value + 1, tail.operations + 2⟩
    | some _ => ⟨tail.value, tail.operations + 1⟩

@[simp] theorem freeCount_value {n : ℕ} (c : Clause n) :
    (freeCount c).value = DNF.freeCount c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [freeCount, DNF.freeCount]
    cases c 0 <;> simp [ih]

theorem freeCount_operations_le {n : ℕ} (c : Clause n) :
    (freeCount c).operations ≤ 2 * n := by
  induction n with
  | zero => simp [freeCount]
  | succ n ih =>
    have h := ih (fun i => c i.succ)
    simp only [freeCount]
    cases c 0 <;> simp only <;> omega

/-- Powers of two are computed by repeated doubling, charging each step. -/
def powerTwo : ℕ → Evaluation ℕ
  | 0 => ⟨1, 0⟩
  | k + 1 =>
    let prev := powerTwo k
    ⟨2 * prev.value, prev.operations + 1⟩

@[simp] theorem powerTwo_value (k : ℕ) : (powerTwo k).value = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [powerTwo, ih, pow_succ, Nat.mul_comm]

@[simp] theorem powerTwo_operations (k : ℕ) : (powerTwo k).operations = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [powerTwo, ih]

/-- Concrete mass evaluation, with a scanned exponent and repeated doubling. -/
def clauseMass {n : ℕ} (c : Clause n) : Evaluation ℕ :=
  let free := freeCount c
  let pow := powerTwo free.value
  ⟨pow.value, free.operations + pow.operations⟩

@[simp] theorem clauseMass_value {n : ℕ} (c : Clause n) :
    (clauseMass c).value = DNF.clauseMass c := by
  simp [clauseMass, DNF.clauseMass]

theorem clauseMass_operations_le {n : ℕ} (c : Clause n) :
    (clauseMass c).operations ≤ 3 * n := by
  have hf := freeCount_operations_le c
  have hn := DNF.freeCount_le c
  simp only [clauseMass, powerTwo_operations, freeCount_value]
  omega

/-- Instrumented unranking: every variable is visited once. A free coordinate
charges parity, division by two, comparison, and construction; a constrained
coordinate only charges the clause lookup and construction. -/
def sampleNat : {n : ℕ} → Clause n → ℕ → Evaluation (Assignment n)
  | 0, _, _ => ⟨Fin.elim0, 0⟩
  | _ + 1, c, r =>
    match c 0 with
    | none =>
      let tail := sampleNat (fun i => c i.succ) (r / 2)
      ⟨Fin.cons (r % 2 == 1) tail.value, tail.operations + 5⟩
    | some b =>
      let tail := sampleNat (fun i => c i.succ) r
      ⟨Fin.cons b tail.value, tail.operations + 2⟩

@[simp] theorem sampleNat_value {n : ℕ} (c : Clause n) (r : ℕ) :
    (sampleNat c r).value = DNF.sampleNat c r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    simp only [sampleNat, DNF.sampleNat]
    cases c 0 <;> simp [ih]

theorem sampleNat_operations_le {n : ℕ} (c : Clause n) (r : ℕ) :
    (sampleNat c r).operations ≤ 5 * n := by
  induction n generalizing r with
  | zero => simp [sampleNat]
  | succ n ih =>
    have h0 := ih (fun i => c i.succ) (r / 2)
    have h1 := ih (fun i => c i.succ) r
    simp only [sampleNat]
    cases c 0 <;> simp only <;> omega

/-- Prefix search instrumented at its actual branch recursion. It computes each
visited clause mass; only the successful branch un-ranks an assignment. -/
def select {n : ℕ} : List (Clause n) → ℕ → Evaluation (Option (ℕ × Assignment n))
  | [], _ => ⟨none, 0⟩
  | c :: cs, r =>
    let mass := clauseMass c
    if r < mass.value then
      let sampled := sampleNat c r
      ⟨some (0, sampled.value), mass.operations + sampled.operations + 1⟩
    else
      let tail := select cs (r - mass.value)
      ⟨tail.value.map (fun p => (p.1 + 1, p.2)), mass.operations + tail.operations + 3⟩

/-- Prefix search uses a polynomial number of unit arithmetic and access
operations, uniformly over every possible (including padded) sample word. -/
theorem select_operations_le {n : ℕ} (cs : List (Clause n)) (r : ℕ) :
    (select cs r).operations ≤ cs.length * (8 * n + 3) := by
  induction cs generalizing r with
  | nil => simp [select]
  | cons c cs ih =>
    have hm := clauseMass_operations_le c
    have hs := sampleNat_operations_le c r
    have ht := ih (r - (clauseMass c).value)
    simp only [select, List.length_cons]
    split <;> simp only
    · nlinarith
    · nlinarith

/-- Short-circuiting membership scan with one list-test operation per visited
clause, plus the cost of the instrumented clause evaluator. -/
def anyClause {n : ℕ} : List (Clause n) → Assignment n → Evaluation Bool
  | [], _ => ⟨false, 0⟩
  | c :: cs, a =>
    let test := evalClause c a
    if test.value then ⟨true, test.operations + 1⟩
    else
      let tail := anyClause cs a
      ⟨tail.value, test.operations + 1 + tail.operations⟩

@[simp] theorem anyClause_value {n : ℕ} (cs : List (Clause n)) (a : Assignment n) :
    (anyClause cs a).value = cs.any (fun c => DNF.evalClause c a) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [anyClause, evalClause_value, List.any_cons]
    cases DNF.evalClause c a <;> simp_all

/-- Owner testing visits at most every preceding clause, never assignments in
its exponentially large satisfaction set. -/
theorem anyClause_operations_le {n : ℕ} (cs : List (Clause n)) (a : Assignment n) :
    (anyClause cs a).operations ≤ cs.length * (3 * n + 1) := by
  induction cs with
  | nil => simp [anyClause]
  | cons c cs ih =>
    have hc := evalClause_operations_le c a
    simp only [anyClause, List.length_cons]
    split <;> simp only
    · nlinarith
    · nlinarith

/-- Explicit repeated evaluation and accumulation. The function `f` supplies
its own instrumented cost, and one addition is charged per sample. -/
def sumEvaluations {α : Type} (f : α → Evaluation ℕ) : List α → Evaluation ℕ
  | [] => ⟨0, 0⟩
  | a :: as =>
    let first := f a
    let tail := sumEvaluations f as
    ⟨first.value + tail.value, first.operations + tail.operations + 1⟩

@[simp] theorem sumEvaluations_value {α : Type} (f : α → Evaluation ℕ) (as : List α) :
    (sumEvaluations f as).value = (as.map (fun a => (f a).value)).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [sumEvaluations, ih]

/-- This is an equality for the cost of the actual recursive loop, including
all per-sample additions. -/
theorem sumEvaluations_operations {α : Type} (f : α → Evaluation ℕ) (as : List α) :
    (sumEvaluations f as).operations =
      (as.map (fun a => (f a).operations)).sum + as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [sumEvaluations, ih]; omega

/-- A uniform cost for the actual sampled calls yields a linear loop bound. -/
theorem sumEvaluations_operations_le {α : Type} (f : α → Evaluation ℕ)
    (as : List α) (bound : ℕ) (h : ∀ a ∈ as, (f a).operations ≤ bound) :
    (sumEvaluations f as).operations ≤ as.length * (bound + 1) := by
  induction as with
  | nil => simp [sumEvaluations]
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [sumEvaluations, List.length_cons]
    nlinarith

/-- Adding independent sample accumulators also has a structural linear bound. -/
theorem nested_sumEvaluations_operations_le {α β : Type}
    (f : α → β → Evaluation ℕ) (as : List α) (bs : List β) (bound : ℕ)
    (h : ∀ a ∈ as, ∀ b ∈ bs, (f a b).operations ≤ bound) :
    (sumEvaluations (fun a => sumEvaluations (f a) bs) as).operations ≤
      as.length * (bs.length * (bound + 1) + 1) := by
  apply sumEvaluations_operations_le
  intro a ha
  exact sumEvaluations_operations_le (f a) bs bound (h a ha)

/-- A list of at most `2^n` masses per term has a linearly bounded total mass. -/
theorem sum_le_length_mul_pow (n : ℕ) (masses : List ℕ)
    (h : ∀ a ∈ masses, a ≤ 2 ^ n) : masses.sum ≤ masses.length * 2 ^ n := by
  induction masses with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.sum_cons, List.length_cons]
    nlinarith

/-- Binary length of a product has an additive upper bound. -/
theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

/-- Magnitude growth in prefix sums is logarithmic in the clause count and
linear in the explicit ambient variable count. -/
theorem sum_size_le (n : ℕ) (masses : List ℕ)
    (h : ∀ a ∈ masses, a ≤ 2 ^ n) :
    masses.sum.size ≤ masses.length.size + n + 1 := by
  calc
    masses.sum.size ≤ (masses.length * 2 ^ n).size :=
      Nat.size_le_size (sum_le_length_mul_pow n masses h)
    _ ≤ masses.length.size + (2 ^ n).size := size_mul_le _ _
    _ = _ := by rw [Nat.size_pow]; omega

/-- Projection to the actual production prefix selector. -/
@[simp] theorem select_value {n : ℕ} (cs : List (Clause n)) (r : ℕ) :
    (select cs r).value = Program.select cs r := by
  induction cs generalizing r with
  | nil => rfl
  | cons c cs ih =>
    simp only [select, clauseMass_value, Program.select]
    split <;> simp [sampleNat_value, ih]

/-- Instrumented prefix materialization; every cons cell copied is charged. -/
def take {α : Type} : ℕ → List α → Evaluation (List α)
  | 0, _ => ⟨[], 0⟩
  | _ + 1, [] => ⟨[], 0⟩
  | k + 1, a :: as =>
    let tail := take k as
    ⟨a :: tail.value, tail.operations + 1⟩

@[simp] theorem take_value {α : Type} (k : ℕ) (as : List α) :
    (take k as).value = as.take k := by
  induction k generalizing as with
  | zero => rfl
  | succ k ih => cases as <;> simp [take, ih]

/-- Exact number of copied list cells. -/
@[simp] theorem take_operations {α : Type} (k : ℕ) (as : List α) :
    (take k as).operations = (as.take k).length := by
  induction k generalizing as with
  | zero => rfl
  | succ k ih => cases as <;> simp [take, ih]

/-- The production owner test, including materializing its prefix and negation. -/
def owner {n : ℕ} (cs : List (Clause n)) (i : ℕ) (a : Assignment n) : Evaluation Bool :=
  let preceding := take i cs
  let found := anyClause preceding.value a
  ⟨!found.value, preceding.operations + found.operations + 1⟩

@[simp] theorem owner_value {n : ℕ} (cs : List (Clause n)) (i : ℕ) (a : Assignment n) :
    (owner cs i a).value = Program.owner cs i a := by
  simp [owner, Program.owner]

theorem owner_operations_le {n : ℕ} (cs : List (Clause n)) (i : ℕ) (a : Assignment n) :
    (owner cs i a).operations ≤ cs.length * (3 * n + 2) + 1 := by
  have ha := anyClause_operations_le (cs.take i) a
  have ht : (cs.take i).length ≤ cs.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
  simp only [owner, take_operations, take_value]
  nlinarith

/-- Actual accumulation of all clause masses. -/
def totalMass {n : ℕ} (cs : List (Clause n)) : Evaluation ℕ :=
  sumEvaluations clauseMass cs

@[simp] theorem totalMass_value {n : ℕ} (cs : List (Clause n)) :
    (totalMass cs).value = Program.totalMass cs := by
  simp [totalMass, Program.totalMass]

theorem totalMass_operations_le {n : ℕ} (cs : List (Clause n)) :
    (totalMass cs).operations ≤ cs.length * (3 * n + 1) := by
  exact sumEvaluations_operations_le clauseMass cs (3 * n)
    (fun c _ => clauseMass_operations_le c)

/-- The total mass and every prefix sum have only linearly many variable bits,
plus logarithmically many bits for the number of clauses. -/
theorem totalMass_size_le {n : ℕ} (cs : List (Clause n)) :
    (Program.totalMass cs).size ≤ cs.length.size + n + 1 := by
  have h := sum_size_le n (cs.map DNF.clauseMass) (by
    intro a ha
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
    exact DNF.clauseMass_le c)
  simpa [Program.totalMass] using h

/-- Bound for the exact finite tape domain accepted by the executable program. -/
theorem randomBitBudget_le {n : ℕ} (cs : List (Clause n)) (samples groups : ℕ) :
    Program.randomBitBudget cs samples groups ≤
      groups * (samples * (cs.length.size + n + 1)) := by
  exact Nat.mul_le_mul_left groups (Nat.mul_le_mul_left samples (totalMass_size_le cs))

/-- The rational request adapter's random-bit budget is polynomial in inverse
accuracy, the explicit variable/term counts, and denominator encoding length.
`reciprocalCeiling` is at most `1/epsilon + 1` for positive requests. -/
theorem requestedBudget_le {n : ℕ} (f : Formula n) (epsilon delta : ℚ) :
    Program.requestedBudget f epsilon delta ≤
      2 * (delta.den.size + 2) *
        (144 * (normalizeFormula f).length * reciprocalCeiling epsilon ^ 2 *
          ((normalizeFormula f).length.size + n + 1)) := by
  let cs := normalizeFormula f
  have h := randomBitBudget_le cs (Program.requestedSamples cs epsilon)
    (Program.requestedGroups delta)
  have hd := confidenceGroups_le_den_size delta
  unfold Program.requestedBudget
  refine h.trans ?_
  simp only [Program.requestedSamples, Program.requestedGroups, samples]
  gcongr

/-- A general integer accumulation bound used for sample numerators. -/
theorem sum_le_length_mul (xs : List ℕ) (q : ℕ) (h : ∀ x ∈ xs, x ≤ q) :
    xs.sum ≤ xs.length * q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons]
    nlinarith

/-- Binary size of the unreduced sample numerator. This controls magnitude
without treating its arithmetic operations as constant-cost bit operations. -/
theorem sample_numerator_size_le {n : ℕ} (cs : List (Clause n)) (samples : ℕ)
    (words : Fin samples → ℕ) :
    ((List.ofFn fun i => Program.trial cs (words i)).sum).size ≤
      samples.size + cs.length.size + n + 2 := by
  have hv : (List.ofFn fun i => Program.trial cs (words i)).sum ≤
      samples * dyadicSize (Program.totalMass cs) := by
    have h := sum_le_length_mul (List.ofFn fun i => Program.trial cs (words i))
      (dyadicSize (Program.totalMass cs)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        exact Program.trial_le_scale cs (words i))
    simpa using h
  have hb := totalMass_size_le cs
  calc
    _ ≤ (samples * dyadicSize (Program.totalMass cs)).size := Nat.size_le_size hv
    _ ≤ samples.size + (dyadicSize (Program.totalMass cs)).size := size_mul_le _ _
    _ = samples.size + (Program.totalMass cs).size + 1 := by
      simp [dyadicSize, dyadicBits, Nat.size_pow]; omega
    _ ≤ _ := by omega

/-- Binary length computed by the same binary recursion as `Nat.size`.
The zero check, low-bit extraction, shift and increment are conservatively
charged by five operations per nonzero recursion node, and one at zero. -/
def bitLength : ℕ → Evaluation ℕ :=
  Nat.binaryRec ⟨0, 1⟩ fun _ _ prev => ⟨prev.value + 1, prev.operations + 5⟩

/-- Both projections are proved by the binary recursion actually executed. -/
theorem bitLength_spec (a : ℕ) :
    (bitLength a).value = a.size ∧ (bitLength a).operations = 5 * a.size + 1 := by
  induction a using Nat.binaryRec' with
  | zero => simp [bitLength]
  | bit b a h ih =>
    have hn : Nat.bit b a ≠ 0 := Nat.bit_ne_zero_iff.mpr h
    simp only [bitLength, Nat.binaryRec_eq b a (Or.inr h), Nat.size_bit hn]
    change (bitLength a).value + 1 = a.size + 1 ∧
      (bitLength a).operations + 5 = 5 * (a.size + 1) + 1
    rcases ih with ⟨hv, hc⟩
    constructor <;> omega

@[simp] theorem bitLength_value (a : ℕ) : (bitLength a).value = a.size :=
  (bitLength_spec a).1

@[simp] theorem bitLength_operations (a : ℕ) :
    (bitLength a).operations = 5 * a.size + 1 := (bitLength_spec a).2

/-- Concrete computation of the scale used on successful trials. -/
def dyadicScale (a : ℕ) : Evaluation ℕ :=
  let width := bitLength a
  let scale := powerTwo width.value
  ⟨scale.value, width.operations + scale.operations⟩

@[simp] theorem dyadicScale_value (a : ℕ) :
    (dyadicScale a).value = dyadicSize a := by
  simp [dyadicScale, dyadicSize, dyadicBits]

@[simp] theorem dyadicScale_operations (a : ℕ) :
    (dyadicScale a).operations = 6 * a.size + 1 := by
  simp [dyadicScale]; omega

/-- Instrumented full trial. Prefix failure skips owner and scale computation;
owner failure skips total-mass and scale computation. -/
def trial {n : ℕ} (cs : List (Clause n)) (r : ℕ) : Evaluation ℕ :=
  let selected := select cs r
  match selected.value with
  | none => ⟨0, selected.operations + 1⟩
  | some (i, a) =>
    let own := owner cs i a
    if own.value then
      let mass := totalMass cs
      let scale := dyadicScale mass.value
      ⟨scale.value, selected.operations + own.operations +
        mass.operations + scale.operations + 2⟩
    else ⟨0, selected.operations + own.operations + 2⟩

@[simp] theorem trial_value {n : ℕ} (cs : List (Clause n)) (r : ℕ) :
    (trial cs r).value = Program.trial cs r := by
  simp only [trial, select_value, Program.trial]
  cases Program.select cs r with
  | none => rfl
  | some p =>
    rcases p with ⟨i, a⟩
    simp only [owner_value]
    split <;> simp

/-- A polynomial bound on the genuine instrumented trial computation. This is
an arithmetic/access bound; its natural-number operands have separately proved
binary-length bounds, and no finite-machine claim is inferred here. -/
theorem trial_operations_le {n : ℕ} (cs : List (Clause n)) (r : ℕ) :
    (trial cs r).operations ≤
      cs.length * (14 * n + 6) + 6 * (cs.length + n + 1) + 4 := by
  have hs := select_operations_le cs r
  have hm := totalMass_operations_le cs
  have hb := totalMass_size_le cs
  have hl : cs.length.size ≤ cs.length := Nat.size_le.mpr Nat.lt_two_pow_self
  cases hv : (select cs r).value with
  | none => simp only [trial, hv]; nlinarith
  | some p =>
    rcases p with ⟨i, a⟩
    have ho := owner_operations_le cs i a
    simp only [trial, hv]
    split_ifs <;> simp only [dyadicScale_operations, totalMass_value] <;> nlinarith

/-- Instrumented tape decoding through the production binary arithmetic
recurrence. Repeated doubling explicitly pays for every power of two. -/
def decode : (b : ℕ) → CoinTape b → Evaluation ℕ
  | 0, _ => ⟨0, 0⟩
  | b + 1, tape =>
    let tail := decode b (Fin.tail tape)
    let pow := powerTwo b
    ⟨tail.value + pow.value * (tape 0).toNat,
      tail.operations + pow.operations + 4⟩

@[simp] theorem decode_value (b : ℕ) (tape : CoinTape b) :
    (decode b tape).value = decodeNat b tape := by
  induction b with
  | zero => rfl
  | succ b ih => simp [decode, decodeNat_succ, ih]

theorem decode_operations_le (b : ℕ) (tape : CoinTape b) :
    (decode b tape).operations ≤ b * (b + 4) := by
  induction b with
  | zero => simp [decode]
  | succ b ih =>
    have ht := ih (Fin.tail tape)
    simp only [decode, powerTwo_operations]
    nlinarith

/-- Recursive accumulation over a finite vector without materializing an
exponentially large state space or a list of assignments. -/
def sumVector : (s : ℕ) → (Fin s → Evaluation ℕ) → Evaluation ℕ
  | 0, _ => ⟨0, 0⟩
  | s + 1, f =>
    let first := f 0
    let tail := sumVector s (fun i => f i.succ)
    ⟨first.value + tail.value, first.operations + tail.operations + 1⟩

@[simp] theorem sumVector_value (s : ℕ) (f : Fin s → Evaluation ℕ) :
    (sumVector s f).value = (List.ofFn fun i => (f i).value).sum := by
  induction s with
  | zero => simp [sumVector]
  | succ s ih => simp [sumVector, List.ofFn_succ, ih]

theorem sumVector_operations_le (s : ℕ) (f : Fin s → Evaluation ℕ)
    (bound : ℕ) (h : ∀ i, (f i).operations ≤ bound) :
    (sumVector s f).operations ≤ s * (bound + 1) := by
  induction s with
  | zero => simp [sumVector]
  | succ s ih =>
    have h0 := h 0
    have ht := ih (fun i => f i.succ) (fun i => h i.succ)
    simp only [sumVector]
    nlinarith

/-- One tape-driven trial combines actual decoding with the complete sampled
trial computation. -/
def tapeTrial {n : ℕ} (cs : List (Clause n))
    (tape : CoinTape (dyadicBits (Program.totalMass cs))) : Evaluation ℕ :=
  let word := decode _ tape
  let answer := trial cs word.value
  ⟨answer.value, word.operations + answer.operations⟩

@[simp] theorem tapeTrial_value {n : ℕ} (cs : List (Clause n))
    (tape : CoinTape (dyadicBits (Program.totalMass cs))) :
    (tapeTrial cs tape).value =
      Program.trial cs (decodeNat (dyadicBits (Program.totalMass cs)) tape) := by
  simp [tapeTrial]

/-- Polynomial arithmetic/access bound including tape decoding. -/
theorem tapeTrial_operations_le {n : ℕ} (cs : List (Clause n))
    (tape : CoinTape (dyadicBits (Program.totalMass cs))) :
    (tapeTrial cs tape).operations ≤
      (cs.length + n + 1) * (cs.length + n + 5) +
      cs.length * (14 * n + 6) + 6 * (cs.length + n + 1) + 4 := by
  have ht := trial_operations_le cs (decode _ tape).value
  have hd := decode_operations_le (dyadicBits (Program.totalMass cs)) tape
  have hb := totalMass_size_le cs
  have hl : cs.length.size ≤ cs.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have hb' : dyadicBits (Program.totalMass cs) ≤ cs.length + n + 1 := by
    unfold dyadicBits; omega
  have hd' : (decode _ tape).operations ≤
      (cs.length + n + 1) * (cs.length + n + 5) := by
    apply hd.trans
    exact Nat.mul_le_mul hb' (by omega)
  simp only [tapeTrial]
  omega

/-- Instrumented group mean, with exact integer accumulation followed by one
rational division. Costs are arithmetic operations, including rational division,
not the bit cost of that division. -/
def groupAverage {n : ℕ} (cs : List (Clause n)) (s : ℕ)
    (tape : CoinTape (s * dyadicBits (Program.totalMass cs))) : Evaluation ℚ :=
  let acc := sumVector s (fun i => tapeTrial cs (Program.coinChunk tape i))
  ⟨(acc.value : ℚ) / (s : ℚ), acc.operations + 1⟩

@[simp] theorem groupAverage_value {n : ℕ} (cs : List (Clause n)) (s : ℕ)
    (tape : CoinTape (s * dyadicBits (Program.totalMass cs))) :
    (groupAverage cs s tape).value = Program.groupAverage cs s tape := by
  simp [groupAverage, Program.groupAverage, Program.naturalAverage]

/-- Explicit polynomial for the actual group evaluator in this intermediate
operation model. There is no hypothesis asserting the desired complexity. -/
theorem groupAverage_operations_le {n : ℕ} (cs : List (Clause n)) (s : ℕ)
    (tape : CoinTape (s * dyadicBits (Program.totalMass cs))) :
    (groupAverage cs s tape).operations ≤
      s * ((cs.length + n + 1) * (cs.length + n + 5) +
        cs.length * (14 * n + 6) + 6 * (cs.length + n + 1) + 5) + 1 := by
  have h := sumVector_operations_le s (fun i => tapeTrial cs (Program.coinChunk tape i))
    _ (fun i => tapeTrial_operations_le cs (Program.coinChunk tape i))
  simp only [groupAverage]
  convert Nat.add_le_add_right h 1 using 1

end Counting.Algorithm.KarpLuby.Cost
