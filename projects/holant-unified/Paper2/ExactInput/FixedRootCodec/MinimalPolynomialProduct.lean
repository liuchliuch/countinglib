import Paper2.ExactInput.FixedRootCodec.Combinators
import Paper2.FixedFieldOutput.LinearMachines
import Mathlib.FieldTheory.Minpoly.ConjRootClass
import Mathlib.FieldTheory.Normal.Closure

/-! A fixed finite conjugate circuit for the minimal polynomial. Repeated
conjugates are removed by exact equality of rational coordinate codes. The
program consists of a fixed number of rational linear maps, equality tests and
field multiplications, without runtime polynomial factorization. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity BinaryCompose FixedFieldMachines
open Polynomial
noncomputable section
variable {E : Type} [Field E] [Algebra ℚ E] {n : ℕ}
local instance : DecidableEq E := Classical.decEq E

def fieldLinearComputes (F : FixedField E n) (A : E →ₗ[ℚ] E) :
    Computes F.encoding F.encoding A :=
  recode (Paper2.FixedFieldOutput.linearComputes
    (F.decode.symm.toLinearMap.comp (A.comp F.decode.toLinearMap)))
    F.decode.symm (fun _ => rfl) (fun x => by
      change (vectorEncoding n).encode (F.decode.symm (A (F.decode (F.decode.symm x)))) =
        (vectorEncoding n).encode (F.decode.symm (A x))
      rw [F.decode.apply_symm_apply])

def conjugateComputes (F : FixedField E n) (σ : E ≃ₐ[ℚ] E) :
    Computes F.encoding F.encoding σ := fieldLinearComputes F σ.toLinearEquiv.toLinearMap

def duplicate (σ : E ≃ₐ[ℚ] E) (tail : List (E ≃ₐ[ℚ] E)) (x : E) : Bool :=
  tail.any (fun τ => decide (σ x = τ x))

def duplicateComputes (F : FixedField E n) (σ : E ≃ₐ[ℚ] E) :
    (tail : List (E ≃ₐ[ℚ] E)) →
      Computes F.encoding encodingBoolBool (duplicate σ tail)
  | [] => constantComputes F.encoding encodingBoolBool false
  | τ :: tail => by
    let h := (pairComputes (conjugateComputes F σ) (conjugateComputes F τ)).andThen
      (equalComputes F.encoding)
    exact congrComputes (ifComputes h (constantComputes F.encoding encodingBoolBool true)
      (duplicateComputes F σ tail)) (fun x => by
        simp only [duplicate,List.any_cons,Function.comp_apply]
        by_cases he : σ x = τ x <;> simp [he])

def conjugateProduct : List (E ≃ₐ[ℚ] E) → E → E[X]
  | [], _ => 1
  | σ :: tail, x =>
    if duplicate σ tail x then conjugateProduct tail x
    else (X - C (σ x)) * conjugateProduct tail x

theorem conjugateProduct_dedup (xs : List (E ≃ₐ[ℚ] E)) (x : E) :
    conjugateProduct xs x = (((xs.map (fun σ => σ x)).dedup).map (fun a => X - C a)).prod := by
  classical
  induction xs with
  | nil => rfl
  | cons σ xs ih =>
    by_cases h : σ x ∈ xs.map (fun τ => τ x)
    · have hd : duplicate σ xs x = true := by
        obtain ⟨τ,hτ,he⟩ := List.mem_map.mp h
        exact List.any_eq_true.mpr ⟨τ,hτ,by simp [he]⟩
      simp [conjugateProduct,hd,ih,List.dedup_cons_of_mem h]
    · have hd : duplicate σ xs x = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        obtain ⟨τ,hτ,he⟩ := List.any_eq_true.mp ht
        exact h (List.mem_map.mpr ⟨τ,hτ,(of_decide_eq_true he).symm⟩)
      simp [conjugateProduct,hd,ih,h]

def coefficientComputes (F : FixedField E n) :
    (xs : List (E ≃ₐ[ℚ] E)) → (k : ℕ) →
      Computes F.encoding F.encoding (fun x => (conjugateProduct xs x).coeff k)
  | [], k => constantComputes F.encoding F.encoding ((1 : E[X]).coeff k)
  | σ :: xs, k => by
    let same := coefficientComputes F xs k
    let shifted : Computes F.encoding F.encoding
        (fun x => (X * conjugateProduct xs x).coeff k) := by
      cases k with
      | zero => exact congrComputes (constantComputes F.encoding F.encoding 0) (fun _ => by simp)
      | succ k => exact congrComputes (coefficientComputes F xs k) (fun _ => by simp)
    let product := (pairComputes (conjugateComputes F σ) same).andThen
      (BellMachines.fieldMultiplication F)
    let next := BellMachines.subComputes F shifted product
    exact congrComputes (ifComputes (duplicateComputes F σ xs) same next) (fun x => by
      simp only [conjugateProduct]
      split
      · rfl
      · simp only [Function.comp_apply,coeff_sub,coeff_C_mul,sub_mul]
      )

def rationalProjection : E →ₗ[ℚ] ℚ := (Algebra.ofId ℚ E).toLinearMap.leftInverse

@[simp] theorem rationalProjection_algebraMap (q : ℚ) :
    rationalProjection (algebraMap ℚ E q) = q := by
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr (algebraMap ℚ E).injective

def rationalProjectionComputes (F : FixedField E n) :
    Computes F.encoding rationalEncoding (rationalProjection (E := E)) := by
  let A : (Fin n → ℚ) →ₗ[ℚ] (Fin 1 → ℚ) :=
    LinearMap.pi (fun _ => (rationalProjection (E := E)).comp F.decode.toLinearMap)
  let coordinates : Computes F.encoding (vectorEncoding 1)
      (fun x => fun _ : Fin 1 => rationalProjection (E := E) x) :=
    recode (Paper2.FixedFieldOutput.linearComputes A) F.decode.symm
      (fun _ => rfl) (fun x => by
        change (vectorEncoding 1).encode (fun _ : Fin 1 =>
          rationalProjection (F.decode (F.decode.symm x))) = _
        rw [F.decode.apply_symm_apply])
  exact congrComputes (coordinates.andThen (coordinateComputes 1 0))
    (fun x => by simp)

theorem conjugateProduct_minpoly [FiniteDimensional ℚ E] [Normal ℚ E]
    (x : E) :
    conjugateProduct (Finset.univ : Finset (E ≃ₐ[ℚ] E)).toList x =
      (minpoly ℚ x).map (algebraMap ℚ E) := by
  classical
  rw [conjugateProduct_dedup]
  let c := ConjRootClass.mk ℚ x
  have hs : ((Finset.univ : Finset (E ≃ₐ[ℚ] E)).toList.map (fun σ => σ x)).toFinset =
      c.carrier.toFinset := by
    ext a
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and,
      Set.mem_toFinset]
    simp only [ConjRootClass.mem_carrier,c,ConjRootClass.mk_eq_mk]
    exact (isConjRoot_iff_exists_algEquiv (K := ℚ) (L := E) (x := a) (y := x)).symm
  have hp := List.prod_toFinset (fun a : E => X - C a)
    (List.nodup_dedup ((Finset.univ : Finset (E ≃ₐ[ℚ] E)).toList.map (fun σ => σ x)))
  rw [← hp,List.toFinset_dedup,hs]
  exact (ConjRootClass.minpoly.map_eq_prod c).symm

theorem conjugateProduct_natDegree_le (xs : List (E ≃ₐ[ℚ] E)) (x : E) :
    (conjugateProduct xs x).natDegree ≤ xs.length := by
  induction xs with
  | nil => simp [conjugateProduct]
  | cons σ xs ih =>
    simp only [conjugateProduct,List.length_cons]
    split
    · omega
    · have hm : ((X - C (σ x)) * conjugateProduct xs x).natDegree ≤
          (X - C (σ x)).natDegree + (conjugateProduct xs x).natDegree := natDegree_mul_le
      exact hm.trans (by simpa [natDegree_X_sub_C,add_comm] using Nat.add_le_add_left ih 1)

end
end Paper2.ExactInput.FixedRootCodec
