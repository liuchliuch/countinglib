import Counting.Model.Holant
import Mathlib.Data.Matrix.Mul

/-!
# Finite-domain ordered tensor actions

Rows are new coordinates, columns are old coordinates. `coordinateAction N f`
acts on column tensors, while `pullback E M = Mᵀ E M` acts on an edge. The
cancellation hypothesis is exactly `M * N = 1`. Transpose is ordinary transpose,
without complex conjugation. No inverse is silently selected.

This generalizes the Boolean algebra in `Holant.Kernel` and
`Holant.BoundaryAction` to a finite domain; the Boolean compatibility and reuse
of the frozen network theorem are proved separately in `Upstream`.
-/

namespace Counting.Algorithm.Holographic

open scoped BigOperators

abbrev Kernel (D R : Type) := Matrix D D R

variable {D R P : Type} [Fintype D] [DecidableEq D] [CommSemiring R]

/-- The tensor product of the supplied matrices at the ordered port indices. -/
def coordinateAction [Fintype P] [DecidableEq P]
    (A : P → Kernel D R) (f : (P → D) → R) : (P → D) → R :=
  fun x => ∑ y : P → D, (∏ j : P, A j (x j) (y j)) * f y

/-- A bilinear edge changes by an ordinary transpose on its first endpoint. -/
def pullback (E M : Kernel D R) : Kernel D R := M.transpose * E * M

@[simp] theorem coordinateAction_one [Fintype P] [DecidableEq P]
    (f : (P → D) → R) : coordinateAction (fun _ => 1) f = f := by
  funext x
  simp only [coordinateAction, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]
  simp

omit [DecidableEq D] in
/-- Matrix multiplication follows the order of successive column actions. -/
theorem coordinateAction_comp [Fintype P] [DecidableEq P]
    (A B : P → Kernel D R) (f : (P → D) → R) :
    coordinateAction A (coordinateAction B f) =
      coordinateAction (fun j => A j * B j) f := by
  funext x
  simp only [coordinateAction, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.prod_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.prod_mul_distrib, mul_assoc]

/-- Each ordered coordinate may have its own explicitly supplied inverse. -/
theorem coordinateAction_cancel [Fintype P] [DecidableEq P]
    (A B : P → Kernel D R) (hAB : ∀ j, A j * B j = 1) (f : (P → D) → R) :
    coordinateAction A (coordinateAction B f) = f := by
  rw [coordinateAction_comp]
  simpa only [hAB] using coordinateAction_one f

/-- Matrix form of edge cancellation. The single displayed right inverse is enough. -/
theorem pullback_cancel (E M N : Kernel D R) (hMN : M * N = 1) :
    N.transpose * pullback E M * N = E := by
  simp only [pullback, Matrix.mul_assoc]
  rw [hMN, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hMN,
    Matrix.transpose_one, Matrix.one_mul]

/-- The same cancellation as an actual double sum over ordered endpoints. -/
theorem edge_cancel (E M N : Kernel D R) (hMN : M * N = 1) (c d : D) :
    (∑ a : D, ∑ b : D, N a c * N b d * pullback E M a b) = E c d := by
  have h := congrFun (congrFun (pullback_cancel E M N hMN) c) d
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply] at h
  rw [Finset.sum_comm] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ac_rfl

omit [DecidableEq D] in
/-- Nullary tables retain their actual scalar, including zero. -/
@[simp] theorem coordinateAction_nullary (N : Kernel D R) (f : (Fin 0 → D) → R) :
    coordinateAction (fun _ => N) f = f := by
  funext x
  simp only [coordinateAction, Fintype.prod_empty, one_mul, Fintype.sum_unique]
  congr 1
  exact Subsingleton.elim _ _

end Counting.Algorithm.Holographic
