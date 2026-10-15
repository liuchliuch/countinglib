import Paper2.Paper1ProvedOddUnaryNRInheritance
import Mathlib.Data.Fin.Tuple.Basic

/-! Coordinate slices preserve actual port order. For arity at least two,
the exact coefficient inheritance of every slice lifts to the entire tensor
by fixing a coordinate different from the coefficient being changed. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [CharZero K]

def slice {n : ℕ} (f : Holant.Signature K (n+1)) (i : Fin (n+1)) (v : Bool) :
    Holant.Signature K n := fun x => f (i.insertNth v x)

@[simp] theorem slice_remove {n : ℕ} (f : Holant.Signature K (n+1))
    (i : Fin (n+1)) (x : Fin (n+1) → Bool) :
    slice f i (x i) (i.removeNth x)=f x := by
  simp [slice,Fin.insertNth_removeNth]

@[simp] theorem slice_update {n : ℕ} (f : Holant.Signature K (n+1))
    (i : Fin (n+1)) (x : Fin (n+1) → Bool) (j : Fin n) (v : Bool) :
    slice f i (x i) (Function.update (i.removeNth x) j v)=
      f (Function.update x (i.succAbove j) v) := by
  simp [slice,Fin.insertNth_update,Fin.insertNth_removeNth]

private theorem other_coordinate {n : ℕ} (i : Fin (n+2)) :
    ∃ j : Fin (n+2), i ≠ j := by
  let z : Fin (n+2) := ⟨0,by omega⟩
  let o : Fin (n+2) := ⟨1,by omega⟩
  by_cases hi : i=z
  · refine ⟨o,?_⟩
    intro he
    have hv := congrArg Fin.val (hi.symm.trans he)
    change (0 : ℕ)=1 at hv
    omega
  · exact ⟨z,hi⟩

/-- Global inheritance follows from actual inheritance of all literal
zero and one coordinate slices; no tensor reconstruction is assumed. -/
theorem inheritance_of_slices {n : ℕ} (f : Holant.Signature K (n+2))
    (hs : ∀ i v, Inheritance (slice f i v)) : Inheritance f := by
  constructor
  · intro x i hi live
    obtain ⟨j,hj⟩ := other_coordinate i
    obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hj
    have hy : (j.removeNth x) k=true := by
      simpa only [Fin.removeNth_apply,hk] using hi
    have hlive : slice f j (x j) (j.removeNth x) ≠ 0 := by simpa using live
    have h := (hs j (x j)).1 (j.removeNth x) k hy hlive
    simpa only [slice_remove,slice_update,hk] using h
  · intro x i hi live
    obtain ⟨j,hj⟩ := other_coordinate i
    obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hj
    have hy : (j.removeNth x) k=false := by
      simpa only [Fin.removeNth_apply,hk] using hi
    have hlive : slice f j (x j) (j.removeNth x) ≠ 0 := by simpa using live
    have h := (hs j (x j)).2 (j.removeNth x) k hy hlive
    simpa only [slice_remove,slice_update,hk] using h

/-- The precise inheritance step used in the high-arity sheared-class case. -/
theorem closed_slices_inheritance {n : ℕ} (f : Holant.Signature K (n+2))
    (hs : ∀ i v, Closed (slice f i v)) : Inheritance f :=
  inheritance_of_slices f (fun i v => closed_inheritance (hs i v))

end
end Paper2.Paper1Proved.OddUnary.NR
