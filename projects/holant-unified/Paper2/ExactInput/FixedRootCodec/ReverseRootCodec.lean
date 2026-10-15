import Paper2.ExactInput.FixedRootCodec.ReverseProjection
import Paper2.ExactInput.FixedRootCodec.VariableRootBisectionCoverage
import Paper2.ExactInput.FixedRootCodec.SturmCounterCorrect

/-! Strict-root decoder assembly from executed varying-polynomial rank
refinement. These composition lemmas require the actual finite root-count
programs; they do not install a presumed root counter or a validity oracle.
The closed instance executes the proved signed-variation count programs. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] {n : ℕ}

abbrev realProjectionCapacity (n : ℕ) := (n+1)*(n+1)+1
abbrev imaginaryProjectionCapacity (n : ℕ) := 2*((n+1)*(n+1))+1
abbrev recoveryPointCapacity (n : ℕ) := realProjectionCapacity n * imaginaryProjectionCapacity n

def recoveryRealPoints (F : FixedField K n)
    (count : VariableRootBisection.CountFunction (realProjectionCapacity n))
    (c : RootCode) : Fin (realProjectionCapacity n) → ℚ :=
  fun j => VariableRootBisection.approximate count j.val
    (inverseRecoveryPrecision F (sparseDenominator c.coefficients)+1) (rootRealProjection n c)

def recoveryImaginaryPoints (F : FixedField K n)
    (count : VariableRootBisection.CountFunction (imaginaryProjectionCapacity n))
    (c : RootCode) : Fin (imaginaryProjectionCapacity n) → ℚ :=
  fun j => VariableRootBisection.approximate count j.val
    (inverseRecoveryPrecision F (sparseDenominator c.coefficients)+1) (rootImaginaryProjection n c)

def recoveryRealPointsComputes (F : FixedField K n)
    (count : VariableRootBisection.CountFunction (realProjectionCapacity n))
    (w : Computes (VariablePolynomial.inputEncoding (realProjectionCapacity n)) encodingNatBool
      (fun p => count p.1 p.2)) :
    Computes rootEncoding (vectorEncoding (realProjectionCapacity n)) (recoveryRealPoints F count) :=
  congrComputes ((pairComputes (rootRecoveryRequestComputes F) (rootRealProjectionComputes n)).andThen
    (VariableRootBisection.approximationVectorComputes count w)) (fun _ => rfl)

def recoveryImaginaryPointsComputes (F : FixedField K n)
    (count : VariableRootBisection.CountFunction (imaginaryProjectionCapacity n))
    (w : Computes (VariablePolynomial.inputEncoding (imaginaryProjectionCapacity n)) encodingNatBool
      (fun p => count p.1 p.2)) :
    Computes rootEncoding (vectorEncoding (imaginaryProjectionCapacity n)) (recoveryImaginaryPoints F count) :=
  congrComputes ((pairComputes (rootRecoveryRequestComputes F) (rootImaginaryProjectionComputes n)).andThen
    (VariableRootBisection.approximationVectorComputes count w)) (fun _ => rfl)

def recoveryPointArray (F : FixedField K n)
    (cr : VariableRootBisection.CountFunction (realProjectionCapacity n))
    (ci : VariableRootBisection.CountFunction (imaginaryProjectionCapacity n))
    (c : RootCode) : (Fin (recoveryPointCapacity n) → ℚ) × (Fin (recoveryPointCapacity n) → ℚ) :=
  (cartesianReal (s := imaginaryProjectionCapacity n) (recoveryRealPoints F cr c),
    cartesianImaginary (r := realProjectionCapacity n) (recoveryImaginaryPoints F ci c))

def recoveryPointArrayComputes (F : FixedField K n)
    (cr : VariableRootBisection.CountFunction (realProjectionCapacity n))
    (ci : VariableRootBisection.CountFunction (imaginaryProjectionCapacity n))
    (wr : Computes (VariablePolynomial.inputEncoding (realProjectionCapacity n)) encodingNatBool
      (fun p => cr p.1 p.2))
    (wi : Computes (VariablePolynomial.inputEncoding (imaginaryProjectionCapacity n)) encodingNatBool
      (fun p => ci p.1 p.2)) :
    Computes rootEncoding (conjugatePointEncoding (recoveryPointCapacity n)) (recoveryPointArray F cr ci) :=
  congrComputes ((pairComputes (recoveryRealPointsComputes F cr wr)
    (recoveryImaginaryPointsComputes F ci wi)).andThen
      (cartesianPointComputes (realProjectionCapacity n) (imaginaryProjectionCapacity n))) (fun _ => rfl)

def reverseRootCoordinatesFromCounts (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (cr : VariableRootBisection.CountFunction (realProjectionCapacity n))
    (ci : VariableRootBisection.CountFunction (imaginaryProjectionCapacity n))
    (c : RootCode) : Fin n → ℚ :=
  rootArrayVerified F e (n+1) (recoveryPointCapacity n) c (recoveryPointArray F cr ci c)

def reverseRootCoordinatesFromCountsComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (cr : VariableRootBisection.CountFunction (realProjectionCapacity n))
    (ci : VariableRootBisection.CountFunction (imaginaryProjectionCapacity n))
    (wr : Computes (VariablePolynomial.inputEncoding (realProjectionCapacity n)) encodingNatBool
      (fun p => cr p.1 p.2))
    (wi : Computes (VariablePolynomial.inputEncoding (imaginaryProjectionCapacity n)) encodingNatBool
      (fun p => ci p.1 p.2)) :
    Computes rootEncoding (vectorEncoding n) (reverseRootCoordinatesFromCounts F e cr ci) :=
  congrComputes ((pairComputes (identityComputes rootEncoding) (recoveryPointArrayComputes F cr ci wr wi)).andThen
    (rootArrayVerifiedComputes F e (n+1) (recoveryPointCapacity n))) (fun _ => rfl)

def reverseRootValueFromCounts (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (cr : VariableRootBisection.CountFunction (realProjectionCapacity n))
    (ci : VariableRootBisection.CountFunction (imaginaryProjectionCapacity n))
    (c : RootCode) : K := F.decode (reverseRootCoordinatesFromCounts F e cr ci c)

def reverseRootValueFromCountsComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (cr : VariableRootBisection.CountFunction (realProjectionCapacity n))
    (ci : VariableRootBisection.CountFunction (imaginaryProjectionCapacity n))
    (wr : Computes (VariablePolynomial.inputEncoding (realProjectionCapacity n)) encodingNatBool
      (fun p => cr p.1 p.2))
    (wi : Computes (VariablePolynomial.inputEncoding (imaginaryProjectionCapacity n)) encodingNatBool
      (fun p => ci p.1 p.2)) :
    Computes rootEncoding F.encoding (reverseRootValueFromCounts F e cr ci) :=
  recode (reverseRootCoordinatesFromCountsComputes F e cr ci wr wi) id (fun _ => rfl)
    (fun _ => (F.encoding_decode _).symm)

theorem reverseRootCoordinatesFromCounts_correct (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (cr : VariableRootBisection.CountFunction (realProjectionCapacity n))
    (ci : VariableRootBisection.CountFunction (imaginaryProjectionCapacity n))
    (c : RootCode) (x : K) (hc : c.MinimalRepresents (e x))
    (hr : ∀ i, ∃ j, |(recoveryRealPoints F cr c j : ℝ)-(conjugateValues F x i).re| ≤
      1/(2 : ℝ)^(inverseRecoveryPrecision F (sparseDenominator c.coefficients)+1))
    (hi : ∀ i, ∃ j, |(recoveryImaginaryPoints F ci c j : ℝ)-(conjugateValues F x i).im| ≤
      1/(2 : ℝ)^(inverseRecoveryPrecision F (sparseDenominator c.coefficients)+1)) :
    F.decode (reverseRootCoordinatesFromCounts F e cr ci c)=x := by
  apply rootArrayVerified_correct F e (n+1) (recoveryPointCapacity n) c x hc
    (Nat.lt_succ_of_le (rootDescriptor_field_degree F e c x hc))
  intro i
  exact cartesianPoint_dyadic_cover (recoveryRealPoints F cr c) (recoveryImaginaryPoints F ci c)
    (conjugateValues F x i) _ (hr i) (hi i)

theorem reverseRootCoordinatesFromCounts_correct_of_counts (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (cr : VariableRootBisection.CountFunction (realProjectionCapacity n))
    (ci : VariableRootBisection.CountFunction (imaginaryProjectionCapacity n))
    (hrc : ∀ v q, cr v q=VariableRootBisection.realRootCount v q)
    (hic : ∀ v q, ci v q=VariableRootBisection.realRootCount v q)
    (c : RootCode) (x : K) (hc : c.MinimalRepresents (e x)) :
    F.decode (reverseRootCoordinatesFromCounts F e cr ci c)=x := by
  apply reverseRootCoordinatesFromCounts_correct F e cr ci c x hc
  · intro i
    have hz := (rootProjection_conjugate_cover F e c x hc i).1
    have hz' : (VariablePolynomial.polynomial (rootRealProjection n c)).aeval
        (conjugateValues F x i).re=0 := by
      simpa only [Polynomial.eval_map,← Polynomial.aeval_def] using hz
    obtain ⟨j,_,hj⟩ := VariableRootBisection.approximationVector_cover cr
      (rootRealProjection n c) (rootProjection_ne_zero n c).1 (hrc _) _ _ hz'
    exact ⟨j,hj.le⟩
  · intro i
    have hz := (rootProjection_conjugate_cover F e c x hc i).2
    have hz' : (VariablePolynomial.polynomial (rootImaginaryProjection n c)).aeval
        (conjugateValues F x i).im=0 := by
      simpa only [Polynomial.eval_map,← Polynomial.aeval_def] using hz
    obtain ⟨j,_,hj⟩ := VariableRootBisection.approximationVector_cover ci
      (rootImaginaryProjection n c) (rootProjection_ne_zero n c).2 (hic _) _ _ hz'
    exact ⟨j,hj.le⟩

def reverseRootCoordinates (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) : RootCode → Fin n → ℚ :=
  reverseRootCoordinatesFromCounts F e VariableRootBisection.realRootCount VariableRootBisection.realRootCount

theorem reverseRootCoordinates_correct (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (c : RootCode) (x : K) (hc : c.MinimalRepresents (e x)) :
    reverseRootCoordinates F e c=F.decode.symm x := by
  apply F.decode.injective
  rw [F.decode.apply_symm_apply]
  exact reverseRootCoordinatesFromCounts_correct_of_counts F e _ _ (fun _ _ => rfl) (fun _ _ => rfl) c x hc

def reverseRootCoordinatesComputesOfCounts (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (wr : Computes (VariablePolynomial.inputEncoding (realProjectionCapacity n)) encodingNatBool
      (fun p => VariableRootBisection.realRootCount p.1 p.2))
    (wi : Computes (VariablePolynomial.inputEncoding (imaginaryProjectionCapacity n)) encodingNatBool
      (fun p => VariableRootBisection.realRootCount p.1 p.2)) :
    Computes rootEncoding (vectorEncoding n) (reverseRootCoordinates F e) :=
  reverseRootCoordinatesFromCountsComputes F e _ _ wr wi

def reverseRootValue (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (c : RootCode) : K :=
  F.decode (reverseRootCoordinates F e c)

theorem reverseRootValue_correct (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (c : RootCode) (x : K) (hc : c.MinimalRepresents (e x)) : reverseRootValue F e c=x := by
  rw [reverseRootValue,reverseRootCoordinates_correct F e c x hc,F.decode.apply_symm_apply]

def reverseRootValueComputesOfCounts (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (wr : Computes (VariablePolynomial.inputEncoding (realProjectionCapacity n)) encodingNatBool
      (fun p => VariableRootBisection.realRootCount p.1 p.2))
    (wi : Computes (VariablePolynomial.inputEncoding (imaginaryProjectionCapacity n)) encodingNatBool
      (fun p => VariableRootBisection.realRootCount p.1 p.2)) :
    Computes rootEncoding F.encoding (reverseRootValue F e) :=
  recode (reverseRootCoordinatesComputesOfCounts F e wr wi) id (fun _ => rfl)
    (fun _ => (F.encoding_decode _).symm)

/-- Closed polynomial finite-machine decoder for every literal public
descriptor representing an element of the fixed field. The actual count
program handles arbitrary runtime polynomials, including repeated roots. -/
def reverseRootCoordinatesComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) :
    Computes rootEncoding (vectorEncoding n) (reverseRootCoordinates F e) :=
  reverseRootCoordinatesComputesOfCounts F e
    (SturmCounter.realRootCountComputes (realProjectionCapacity n))
    (SturmCounter.realRootCountComputes (imaginaryProjectionCapacity n))

def reverseRootValueComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) :
    Computes rootEncoding F.encoding (reverseRootValue F e) :=
  recode (reverseRootCoordinatesComputes F e) id (fun _ => rfl)
    (fun _ => (F.encoding_decode _).symm)

end
end Paper2.ExactInput.FixedRootCodec
