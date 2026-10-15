import Counting.Algorithm.KarpLuby.DNFSampling
import Counting.Algorithm.KarpLuby.Dyadic
import Counting.Algorithm.KarpLuby.Confidence
import Counting.Algorithm.KarpLuby.Parameters
import Counting.Algorithm.KarpLuby.Encoding

/-!
# Executable bounded-tape DNF estimator

The algorithm scans clause prefix masses and un-ranks an assignment inside one
clause. It never enumerates the Boolean assignment space. Every source of
randomness is a coordinate of a finite Boolean tape. Words outside the tagged
union return zero immediately; no rejection loop is used.

`estimate` exposes the integer sample/group parameters independently of their
probabilistic justification. `run` is a total rational-parameter adapter;
correctness assumptions and the machine-cost refinement remain separate theorems.
-/

namespace Counting.Algorithm.KarpLuby.Program

open DNF

variable {n : ℕ}

/-- Cardinality of the tagged union, with duplicate clauses retained. -/
def totalMass (cs : List (Clause n)) : ℕ := (cs.map clauseMass).sum

@[simp] theorem totalMass_nil : totalMass ([] : List (Clause n)) = 0 := rfl

@[simp] theorem totalMass_cons (c : Clause n) (cs : List (Clause n)) :
    totalMass (c :: cs) = clauseMass c + totalMass cs := rfl

/-- Locate a tagged assignment by consecutive clause intervals. -/
def select : List (Clause n) → ℕ → Option (ℕ × Assignment n)
  | [], _ => none
  | c :: cs, r =>
      if r < clauseMass c then some (0, sampleNat c r)
      else (select cs (r - clauseMass c)).map fun p => (p.1 + 1, p.2)

@[simp] theorem select_nil (r : ℕ) : select ([] : List (Clause n)) r = none := rfl

/-- Prefix selection rejects exactly the padding outside the tagged union. -/
theorem select_eq_none_iff (cs : List (Clause n)) (r : ℕ) :
    select cs r = none ↔ totalMass cs ≤ r := by
  induction cs generalizing r with
  | nil => simp [select, totalMass]
  | cons c cs ih =>
      simp only [select, totalMass_cons]
      split_ifs with h
      · simp only [false_iff]
        omega
      · simp only [Option.map_eq_none_iff, ih]
        omega

/-- Ownership is decided by scanning clauses before the selected occurrence. -/
def owner (cs : List (Clause n)) (i : ℕ) (a : Assignment n) : Bool :=
  !(cs.take i).any fun c => evalClause c a

@[simp] theorem owner_zero (cs : List (Clause n)) (a : Assignment n) :
    owner cs 0 a = true := rfl

/-- A dyadic trial is zero or the dyadic scale. -/
def trial (cs : List (Clause n)) (r : ℕ) : ℕ :=
  match select cs r with
  | none => 0
  | some (i, a) => if owner cs i a then dyadicSize (totalMass cs) else 0

theorem trial_eq_zero_or_scale (cs : List (Clause n)) (r : ℕ) :
    trial cs r = 0 ∨ trial cs r = dyadicSize (totalMass cs) := by
  unfold trial
  split
  · exact Or.inl rfl
  · split <;> simp

theorem trial_le_scale (cs : List (Clause n)) (r : ℕ) :
    trial cs r ≤ dyadicSize (totalMass cs) := by
  rcases trial_eq_zero_or_scale cs r with h | h <;> simp [h]

theorem trial_of_mass_le (cs : List (Clause n)) (r : ℕ) (h : totalMass cs ≤ r) :
    trial cs r = 0 := by simp [trial, (select_eq_none_iff cs r).mpr h]

@[simp] theorem trial_nil (r : ℕ) : trial ([] : List (Clause n)) r = 0 := rfl

theorem trial_of_zero_mass (cs : List (Clause n)) (h : totalMass cs = 0) (r : ℕ) :
    trial cs r = 0 := trial_of_mass_le cs r (by omega)

/-- A disjoint fixed-width block of a finite tape. -/
def coinChunk {width blocks : ℕ} (tape : CoinTape (blocks * width))
    (block : Fin blocks) : CoinTape width := fun bit =>
  tape ⟨block.val * width + bit.val, by
    calc
      block.val * width + bit.val < block.val * width + width :=
        Nat.add_lt_add_left bit.isLt _
      _ = (block.val + 1) * width := by simp [Nat.add_mul]
      _ ≤ blocks * width := Nat.mul_le_mul_right width block.isLt⟩

/-- The exact number of coordinates in the input tape. -/
def randomBitBudget (cs : List (Clause n)) (samples groups : ℕ) : ℕ :=
  groups * (samples * dyadicBits (totalMass cs))

/-- Natural accumulation keeps intermediate numerators integral. -/
def naturalAverage (samples : ℕ) (f : Fin samples → ℕ) : ℚ :=
  ((List.ofFn f).sum : ℚ) / (samples : ℚ)

@[simp] theorem naturalAverage_zero (f : Fin 0 → ℕ) : naturalAverage 0 f = 0 := by
  simp [naturalAverage]

/-- One independent block of trials, interpreted as a rational mean. -/
def groupAverage (cs : List (Clause n)) (samples : ℕ)
    (tape : CoinTape (samples * dyadicBits (totalMass cs))) : ℚ :=
  naturalAverage samples fun s =>
    trial cs (decodeNat (dyadicBits (totalMass cs)) (coinChunk tape s))

/-- Radius-free aggregation; neither the true count nor an error radius is an input. -/
def estimate (cs : List (Clause n)) (samples groups : ℕ)
    (tape : CoinTape (randomBitBudget cs samples groups)) : ℚ :=
  median groups fun g => groupAverage cs samples (coinChunk tape g)

/-- Sample size with the conservative concentration constant used by the PAC layer. -/
def requestedSamples (cs : List (Clause n)) (epsilon : ℚ) : ℕ :=
  samples cs.length epsilon

/-- Twice a logarithmic number of groups, always positive. -/
def requestedGroups (delta : ℚ) : ℕ :=
  2 * confidenceGroups delta

/-- Correctness of the rational front end is intended for these parameters. -/
def ValidRequest (epsilon delta : ℚ) : Prop :=
  0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < delta ∧ delta < 1

/-- Exact budget, computed after contradictory terms have been removed. -/
def requestedBudget (f : Formula n) (epsilon delta : ℚ) : ℕ :=
  let cs := normalizeFormula f
  randomBitBudget cs (requestedSamples cs epsilon) (requestedGroups delta)

/-- A total executable adapter from explicit DNF and rational accuracy parameters. -/
def run (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (requestedBudget f epsilon delta)) : ℚ :=
  let cs := normalizeFormula f
  estimate cs (requestedSamples cs epsilon) (requestedGroups delta) tape

/-- Canonical rational output encoding uses an integer numerator and positive denominator. -/
def encodeOutput (q : ℚ) : ℤ × ℕ := (q.num, q.den)

theorem encodeOutput_den_pos (q : ℚ) : 0 < (encodeOutput q).2 := q.pos

theorem decode_encodeOutput (q : ℚ) :
    ((encodeOutput q).1 : ℚ) / ((encodeOutput q).2 : ℚ) = q := by
  exact q.num_div_den

/-- The concrete random program returns the canonical framed binary rational code. -/
def runEncoded (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (requestedBudget f epsilon delta)) : List Bool :=
  Encoding.encodeOutput (run f epsilon delta tape)

/-- Decoding the actual program output recovers precisely the rational estimate. -/
@[simp] theorem decode_runEncoded (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (requestedBudget f epsilon delta)) :
    Encoding.decodeOutput (runEncoded f epsilon delta tape) =
      some (run f epsilon delta tape) := Encoding.decode_encodeOutput _

end Counting.Algorithm.KarpLuby.Program
