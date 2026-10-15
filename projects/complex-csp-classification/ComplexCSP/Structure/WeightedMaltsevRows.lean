import ComplexCSP.Structure.MaltsevTypeSplit
import ComplexCSP.Complexity.RowNormalization

/-!
# Materialized canonical row labels for weighted elimination

The actual row and its normalized coordinates are vectors, so stored labels
never re-evaluate a recursively computed marginal through a function closure.
-/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness
open scoped BigOperators
variable {K : Type} [Field K] [DecidableEq K] {d n : ℕ}

abbrev RowLabel (K : Type) (d : ℕ) := Option (Fin d × Vector K d)

def snocTuple (x : Tuple (Fin d) n) (a : Fin d) : Tuple (Fin d) (n + 1) :=
  Vector.ofFn (Fin.snoc (view x) a)

@[simp] theorem view_snocTuple (x : Tuple (Fin d) n) (a : Fin d) :
    view (snocTuple x a) = Fin.snoc (view x) a := view_ofFn _

def decodeLabel (L : RowLabel K d) : ComplexityRowNormalization.Result K d :=
  L.map (fun p => (p.1, view p.2))

def materializeLabel (L : ComplexityRowNormalization.Result K d) : RowLabel K d :=
  L.map (fun p => (p.1, Vector.ofFn p.2))

omit [Field K] [DecidableEq K] in
@[simp] theorem decode_materialize (L : ComplexityRowNormalization.Result K d) :
    decodeLabel (materializeLabel L) = L := by
  cases L with
  | none => rfl
  | some p => rcases p with ⟨i, v⟩; simp [decodeLabel, materializeLabel]

omit [Field K] [DecidableEq K] in
@[simp] theorem materialize_decode (L : RowLabel K d) :
    materializeLabel (decodeLabel L) = L := by
  cases L with
  | none => rfl
  | some p =>
    rcases p with ⟨i, v⟩
    simp only [materializeLabel, decodeLabel, Option.map_some]
    congr 2
    exact view_injective (view_ofFn (view v))

def normalizedRow (v : Vector K d) : RowLabel K d :=
  materializeLabel (ComplexityRowNormalization.normalize (view v))

@[simp] theorem normalizedRow_none (v : Vector K d) :
    normalizedRow v = none ↔ view v = 0 := by
  constructor
  · intro h
    have he := congrArg decodeLabel h
    rw [normalizedRow, decode_materialize] at he
    exact (ComplexityRowNormalization.normalize_none_iff (view v)).mp he
  · intro h
    simp [normalizedRow, h, materializeLabel]

theorem normalizedRow_spec (v : Vector K d) (a : Fin d) (w : Vector K d)
    (h : normalizedRow v = some (a, w)) :
    view v a ≠ 0 ∧ view w a = 1 ∧ ∀ j, view v j = view v a * view w j := by
  have he := congrArg decodeLabel h
  rw [normalizedRow, decode_materialize] at he
  exact ComplexityRowNormalization.normalize_some_spec (view v) a (view w) he

def labelFactor (L : RowLabel K d) : K :=
  match L with
  | none => 0
  | some p => ∑ j, view p.2 j

theorem normalizedRow_sum (v : Vector K d) (a : Fin d) (w : Vector K d)
    (h : normalizedRow v = some (a, w)) :
    (∑ j, view v j) = view v a * labelFactor (some (a, w)) := by
  obtain ⟨_, _, hr⟩ := normalizedRow_spec v a w h
  calc
    (∑ j, view v j) = ∑ j, view v a * view w j := Finset.sum_congr rfl (fun j _ => hr j)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Materialize the actual next-stage row before normalizing. -/
def rowLabel (evaluate : Tuple (Fin d) (n + 1) → K) (x : Tuple (Fin d) n) : RowLabel K d :=
  normalizedRow (Vector.ofFn (fun a => evaluate (snocTuple x a)))

def tableRows (G : (Fin (n + 1) → Fin d) → K) (x : Fin n → Fin d) : Fin d → K :=
  fun a => G (Fin.snoc x a)

def tableLabel (G : (Fin (n + 1) → Fin d) → K) (x : Fin n → Fin d) : RowLabel K d :=
  normalizedRow (Vector.ofFn (tableRows G x))

def rowSupport (G : (Fin (n + 1) → Fin d) → K) : Set (Fin n → Fin d) :=
  {x | tableRows G x ≠ 0}

def marginal (G : (Fin (n + 1) → Fin d) → K) : (Fin n → Fin d) → K :=
  fun x => ∑ a, tableRows G x a

@[simp] theorem tableLabel_none (G : (Fin (n + 1) → Fin d) → K) (x : Fin n → Fin d) :
    tableLabel G x = none ↔ tableRows G x = 0 := by simp [tableLabel]

omit [DecidableEq K] in
theorem marginal_zero_of_row_zero (G : (Fin (n + 1) → Fin d) → K)
    (x : Fin n → Fin d) (hx : tableRows G x = 0) : marginal G x = 0 := by simp [marginal, hx]

theorem marginal_factor (G : (Fin (n + 1) → Fin d) → K) (x : Fin n → Fin d)
    (a : Fin d) (w : Vector K d) (h : tableLabel G x = some (a, w)) :
    marginal G x = G (Fin.snoc x a) * labelFactor (some (a, w)) := by
  simpa only [view_ofFn, marginal, tableRows] using normalizedRow_sum (Vector.ofFn (tableRows G x)) a w h

theorem marginal_nonzero_iff (G : (Fin (n + 1) → Fin d) → K) (x : Fin n → Fin d) :
    marginal G x ≠ 0 ↔ x ∈ rowSupport G ∧ labelFactor (tableLabel G x) ≠ 0 := by
  cases hl : tableLabel G x with
  | none =>
    have hz := (tableLabel_none G x).mp hl
    simp [marginal_zero_of_row_zero G x hz, rowSupport, hz, labelFactor]
  | some p =>
    rcases p with ⟨a, w⟩
    have hs := normalizedRow_spec (Vector.ofFn (tableRows G x)) a w hl
    have hrow : tableRows G x ≠ 0 := by
      intro hz
      exact hs.1 (by simp [hz])
    have ha : G (Fin.snoc x a) ≠ 0 := by simpa only [view_ofFn, tableRows] using hs.1
    rw [marginal_factor G x a w hl]
    simp [ha, rowSupport, hrow]


end ComplexCSP.WeightedMaltsev
