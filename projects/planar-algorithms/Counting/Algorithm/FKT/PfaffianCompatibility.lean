import PlanarHom.OccurrencePfaffianEvaluationMachines
import Counting.Algorithm.PfaffianFinite

/-!
# Compatibility with the frozen A1 Pfaffian evaluator

The canonical PlanarHom pipeline and frozen A1 retain two namespaces for the
same original source closure. These equalities make that relationship explicit
for the actual row program and external codecs. They do not identify distinct
graph structures or arbitrary chosen source machine witnesses.
-/

noncomputable section

namespace Counting.Algorithm.FKT.PfaffianCompatibility

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}

/-- The canonical and A1 row programs are definitionally the same algorithm. -/
theorem evaluateGrid_eq (g : PlanarHom.PfaffianList.Grid K) :
    PlanarHom.PfaffianList.evaluateGrid g =
      Counting.Algorithm.Pfaffian.evaluateGrid g := rfl

/-- The same literal matrix rows feed both programs. -/
theorem matrixRows_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    PlanarHom.PfaffianList.matrixRows A = Counting.Algorithm.Pfaffian.matrixRows A := rfl

private theorem frame_eq (word : List Bool) :
    PlanarHom.Complexity.BitEncoding.frame word =
      PfaffianPort.Complexity.BitEncoding.frame word := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    simp only [PlanarHom.Complexity.BitEncoding.frame,
      PfaffianPort.Complexity.BitEncoding.frame, ih]

private theorem frames_eq (words : List (List Bool)) :
    PlanarHom.Complexity.BitEncoding.frames words =
      PfaffianPort.Complexity.BitEncoding.frames words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [PlanarHom.Complexity.BitEncoding.frames,
      PfaffianPort.Complexity.BitEncoding.frames, frame_eq, ih]

private theorem int_encode_eq (z : ℤ) :
    PlanarHom.Complexity.BitEncoding.int.encode z =
      PfaffianPort.Complexity.BitEncoding.int.encode z := by
  cases z <;> simp only [PlanarHom.Complexity.BitEncoding.int,
    PfaffianPort.Complexity.BitEncoding.int, PlanarHom.Complexity.BitEncoding.retract,
    PfaffianPort.Complexity.BitEncoding.retract, PlanarHom.Complexity.BitEncoding.prod,
    PfaffianPort.Complexity.BitEncoding.prod, PlanarHom.Complexity.BitEncoding.bool,
    PfaffianPort.Complexity.BitEncoding.bool, PlanarHom.Complexity.BitEncoding.nat,
    PfaffianPort.Complexity.BitEncoding.nat, frame_eq]

private theorem rat_encode_eq : PlanarHom.Complexity.BitEncoding.rat.encode =
    PfaffianPort.Complexity.BitEncoding.rat.encode := by
  funext q
  simp only [PlanarHom.Complexity.BitEncoding.rat,
    PfaffianPort.Complexity.BitEncoding.rat, PlanarHom.Complexity.BitEncoding.retract,
    PfaffianPort.Complexity.BitEncoding.retract, PlanarHom.Complexity.BitEncoding.prod,
    PfaffianPort.Complexity.BitEncoding.prod, int_encode_eq, frame_eq]
  rfl

private theorem list_encode_eq {α : Type}
    (a : PlanarHom.Complexity.BitEncoding α) (b : PfaffianPort.Complexity.BitEncoding α)
    (h : a.encode = b.encode) : a.list.encode = b.list.encode := by
  funext xs
  simp only [PlanarHom.Complexity.BitEncoding.list, PfaffianPort.Complexity.BitEncoding.list,
    PlanarHom.Complexity.BitEncoding.nat, PfaffianPort.Complexity.BitEncoding.nat,
    frame_eq, frames_eq, h]

/-- The fixed-basis field codecs produce exactly the same literal words. -/
theorem numberFieldEncoding_encode_eq (basis : Module.Basis (Fin dimension) ℚ K) :
    (PlanarHom.Complexity.numberFieldEncoding basis).encode =
      (PfaffianPort.Complexity.numberFieldEncoding basis).encode := by
  funext x
  simp only [PlanarHom.Complexity.numberFieldEncoding,
    PfaffianPort.Complexity.numberFieldEncoding, PlanarHom.Complexity.rationalCoordinates,
    PfaffianPort.Complexity.rationalCoordinates, PlanarHom.Complexity.BitEncoding.retract,
    PfaffianPort.Complexity.BitEncoding.retract, PlanarHom.Complexity.BitEncoding.vector,
    PfaffianPort.Complexity.BitEncoding.vector, list_encode_eq _ _ rat_encode_eq]

/-- The nested row codecs retain every input bit, including ragged grids. -/
theorem gridEncoding_encode_eq (basis : Module.Basis (Fin dimension) ℚ K) :
    (PlanarHom.PfaffianList.gridEncoding basis).encode =
      (Counting.Algorithm.Pfaffian.gridEncoding basis).encode :=
  list_encode_eq _ _ (list_encode_eq _ _ (numberFieldEncoding_encode_eq basis))

/-- Repackage the accepted A1 finite machine with the canonical codecs. The
machine and numerical step witness are kept literally; only correctness proofs
are transported along the proved equality of external words. -/
def sharedComputer (basis : Module.Basis (Fin dimension) ℚ K) :
    Counting.Computation.PolyTime (PlanarHom.PfaffianList.gridEncoding basis).toFinEncoding
      (PlanarHom.Complexity.numberFieldEncoding basis).toFinEncoding
      (PlanarHom.PfaffianList.evaluateGrid (K := K)) where
  toTM2ComputableAux := (Counting.Algorithm.PfaffianFinite.evaluateGridPolyTime basis).toTM2ComputableAux
  time := (Counting.Algorithm.PfaffianFinite.evaluateGridPolyTime basis).time
  finiteAlphabets := (Counting.Algorithm.PfaffianFinite.evaluateGridPolyTime basis).finiteAlphabets
  outputsFun g := {
    steps := ((Counting.Algorithm.PfaffianFinite.evaluateGridPolyTime basis).outputsFun g).steps
    evals_in_steps := by
      simpa only [PlanarHom.Complexity.BitEncoding.toFinEncoding,
        PfaffianPort.Complexity.BitEncoding.toFinEncoding,
        gridEncoding_encode_eq, numberFieldEncoding_encode_eq, evaluateGrid_eq] using
        ((Counting.Algorithm.PfaffianFinite.evaluateGridPolyTime basis).outputsFun g).evals_in_steps
    steps_le_m := by
      simpa only [PlanarHom.Complexity.BitEncoding.toFinEncoding,
        PfaffianPort.Complexity.BitEncoding.toFinEncoding, gridEncoding_encode_eq] using
        ((Counting.Algorithm.PfaffianFinite.evaluateGridPolyTime basis).outputsFun g).steps_le_m }

/-- The same finite machine, input alphabet and output alphabet are reused. -/
theorem sharedComputer_aux_eq (basis : Module.Basis (Fin dimension) ℚ K) :
    (sharedComputer basis).toTM2ComputableAux =
      (Counting.Algorithm.PfaffianFinite.evaluateGridPolyTime basis).toTM2ComputableAux := rfl

@[simp] theorem sharedComputer_time (basis : Module.Basis (Fin dimension) ℚ K) :
    (sharedComputer basis).time =
      (Counting.Algorithm.PfaffianFinite.sourceComputer basis).time := rfl

@[simp] theorem sharedComputer_steps (basis : Module.Basis (Fin dimension) ℚ K)
    (g : PlanarHom.PfaffianList.Grid K) :
    ((sharedComputer basis).outputsFun g).steps =
      ((Counting.Algorithm.PfaffianFinite.sourceComputer basis).outputsFun g).steps := rfl

end Counting.Algorithm.FKT.PfaffianCompatibility
