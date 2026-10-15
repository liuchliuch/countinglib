import Paper2.ExactInput.FixedRootCodec.ReverseValidation
import Paper2.ExactInput.FixedRootCodec.ReverseSelection
import Paper2.ExactInput.FixedRootCodec.ReverseFieldCandidates

/-! The exact final stage of strict-root decoding. Its runtime input contains
the literal descriptor and a finite rational candidate array. Extra points
and repetitions are harmless: the exact polynomial-and-rectangle verifier
filters them after all fixed embedding assignments have been recovered. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] {n d : ℕ}

abbrev rootCandidateArrayEncoding (d : ℕ) := pairEncoding rootEncoding (conjugatePointEncoding d)

def rootArrayCandidate (F : FixedField K n) (d : ℕ)
    (c : RootCode) (v : (Fin d → ℚ) × (Fin d → ℚ)) (index : Fin (d^n)) : Fin n → ℚ :=
  inverseCandidate F (sparseDenominator c.coefficients) v.1 v.2 (assignmentEnumeration n d index)

def rootArrayCandidateComputes (F : FixedField K n) (d : ℕ) (index : Fin (d^n)) :
    Computes (rootCandidateArrayEncoding d) (vectorEncoding n)
      (fun p => rootArrayCandidate F d p.1 p.2 index) := by
  let D := (Wiring.firstComputes rootEncoding (conjugatePointEncoding d)).andThen rootDenominatorComputes
  let points := Wiring.secondComputes rootEncoding (conjugatePointEncoding d)
  exact congrComputes ((pairComputes D points).andThen
    (inverseCandidateComputes F d (assignmentEnumeration n d index))) (fun _ => rfl)

def rootArrayVerified (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (N d : ℕ)
    (c : RootCode) (v : (Fin d → ℚ) × (Fin d → ℚ)) : Fin n → ℚ :=
  firstVerified 0 (d^n)
    (fun i => fieldRootCandidate F e N c (rootArrayCandidate F d c v i))
    (rootArrayCandidate F d c v)

def rootArrayVerifiedComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (N d : ℕ) :
    Computes (rootCandidateArrayEncoding d) (vectorEncoding n)
      (fun p => rootArrayVerified F e N d p.1 p.2) := by
  let c := Wiring.firstComputes rootEncoding (conjugatePointEncoding d)
  let candidate := rootArrayCandidateComputes F d
  exact firstVerifiedComputes (rootCandidateArrayEncoding d) (vectorEncoding n) 0 (d^n)
    (fun p i => fieldRootCandidate F e N p.1 (rootArrayCandidate F d p.1 p.2 i))
    (fun p i => rootArrayCandidate F d p.1 p.2 i)
    (fun i => congrComputes ((pairComputes c (candidate i)).andThen
      (fieldRootCandidateComputes F e N)) (fun _ => rfl)) candidate

theorem rootArrayVerified_correct (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (N d : ℕ)
    (c : RootCode) (x : K) (hc : c.MinimalRepresents (e x))
    (hd : c.polynomial.natDegree<N) (v : (Fin d → ℚ) × (Fin d → ℚ))
    (cover : ∀ i, ∃ j, ‖rationalComplexPoint v.1 v.2 j-conjugateValues F x i‖ ≤
      1/(2 : ℝ)^(inverseRecoveryPrecision F (sparseDenominator c.coefficients))) :
    F.decode (rootArrayVerified F e N d c v)=x := by
  have hroot : Polynomial.aeval x c.polynomial=0 := by
    apply e.injective
    change e (Polynomial.aeval x c.polynomial)=e 0
    rw [← Polynomial.aeval_algHom_apply e x c.polynomial,map_zero]
    exact hc.1.2.2.1
  have hint := sparseDenominator_integral_root c.coefficients hc.2.1 x hroot
  obtain ⟨i,hi⟩ := inverseCandidate_exists F (sparseDenominator c.coefficients)
    (sparseDenominator_pos c.coefficients) v.1 v.2 x hint cover
  have heq : F.decode (fun j => F.basis.repr x j)=x := by
    change F.basis.equivFun.symm (F.basis.equivFun x)=x
    exact F.basis.equivFun.symm_apply_apply x
  apply firstVerified_satisfies 0 (fun w => F.decode w=x)
  · intro j hj
    exact (fieldRootCandidate_correct F e N c x hc hd _).mp hj
  · refine ⟨i,(fieldRootCandidate_correct F e N c x hc hd _).mpr ?_⟩
    change F.decode (inverseCandidate F (sparseDenominator c.coefficients) v.1 v.2
      (assignmentEnumeration n d i))=x
    rw [hi]
    exact heq

end
end Paper2.ExactInput.FixedRootCodec
