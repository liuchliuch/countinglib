import Paper2.ExactInput.FixedRootCodec.ReverseFieldNumerical

/-! Every assignment of a fixed-capacity root candidate array to the fixed
field embeddings has its own finite rational program. The actual precision
scanner uses only the binary length of the computed common denominator plus
a constant belonging to the fixed field. Candidate arrays may contain extra
points and repetitions: correctness needs only one assignment approximating
the genuine conjugate tuple. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines GraphPreprocessing
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] {n d : ℕ}

theorem inverseNorm_exponent_exists (F : FixedField K n) :
    ∃ E : ℕ, ∀ i : Fin n, 2 + inverseRowNorm F i ≤ (2 : ℝ)^E := by
  obtain ⟨E,hE⟩ := exists_nat_ge (2 + ∑ i, inverseRowNorm F i)
  refine ⟨E,fun i => ?_⟩
  have hi : inverseRowNorm F i ≤ ∑ j, inverseRowNorm F j :=
    Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (Finset.mem_univ i)
  have hh : 2 + inverseRowNorm F i ≤ 2 + ∑ j, inverseRowNorm F j := by linarith
  apply hh.trans (hE.trans ?_)
  exact_mod_cast (Nat.lt_two_pow_self (n := E)).le

def inverseNormExponent (F : FixedField K n) : ℕ :=
  Classical.choose (inverseNorm_exponent_exists F)

theorem inverseNormExponent_bound (F : FixedField K n) (i : Fin n) :
    2 + inverseRowNorm F i ≤ (2 : ℝ)^(inverseNormExponent F) :=
  Classical.choose_spec (inverseNorm_exponent_exists F) i

def inverseRecoveryOffset (F : FixedField K n) : ℕ :=
  (coordinateLatticeDenominator F).size + inverseNormExponent F + 2

def inverseRecoveryPrecision (F : FixedField K n) (D : ℕ) : ℕ :=
  (encodingNatBool.encode D).length + inverseRecoveryOffset F

def inverseRecoveryPrecisionComputes (F : FixedField K n) :
    Computes encodingNatBool UnaryBinary.unaryEncoding (inverseRecoveryPrecision F) :=
  congrComputes (precisionComputes encodingNatBool 1 (inverseRecoveryOffset F))
    (fun D => by simp [inverseRecoveryPrecision])

theorem inverseRecoveryPrecision_eq (F : FixedField K n) (D : ℕ) :
    inverseRecoveryPrecision F D = D.size +
      (coordinateLatticeDenominator F).size + inverseNormExponent F + 2 := by
  simp [inverseRecoveryPrecision,inverseRecoveryOffset,encodingNatBool,encodeNat_length,
    Nat.add_assoc]

theorem inverseRecoveryPrecision_accuracy (F : FixedField K n) (D : ℕ) (hD : 0 < D)
    (i : Fin n) :
    2/(2 : ℝ)^(inverseRecoveryPrecision F D) +
      (1/(2 : ℝ)^(inverseRecoveryPrecision F D)) * inverseRowNorm F i ≤
      1/(2 * (coordinateLatticeDenominator F * D : ℕ) : ℝ) := by
  let C := coordinateLatticeDenominator F
  have hC : 0 < C := coordinateLatticeDenominator_pos F
  have hCD : (0 : ℝ) < (C*D : ℕ) := by exact_mod_cast Nat.mul_pos hC hD
  have hn : ((C*D : ℕ) : ℝ) ≤ (2 : ℝ)^(C.size+D.size) := by
    have hc := (Nat.lt_size_self C).le
    have hd := (Nat.lt_size_self D).le
    have h := Nat.mul_le_mul hc hd
    rw [← pow_add] at h
    exact_mod_cast h
  have he : (2 : ℝ)^(inverseNormExponent F) /
      (2 : ℝ)^(inverseRecoveryPrecision F D) =
      1/(4 * (2 : ℝ)^(C.size+D.size)) := by
    rw [inverseRecoveryPrecision_eq]
    change (2 : ℝ)^(inverseNormExponent F) /
      (2 : ℝ)^(D.size+C.size+inverseNormExponent F+2) = _
    rw [show D.size+C.size+inverseNormExponent F+2 =
      inverseNormExponent F+(C.size+D.size+2) by omega,pow_add,pow_add]
    norm_num
    field_simp
  calc
    _ = (2 + inverseRowNorm F i)/(2 : ℝ)^(inverseRecoveryPrecision F D) := by ring
    _ ≤ (2 : ℝ)^(inverseNormExponent F)/(2 : ℝ)^(inverseRecoveryPrecision F D) :=
      div_le_div_of_nonneg_right (inverseNormExponent_bound F i) (by positivity)
    _ = 1/(4 * (2 : ℝ)^(C.size+D.size)) := he
    _ ≤ 1/(2 * ((C*D : ℕ) : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith

def assignmentEnumeration (n d : ℕ) : Fin (d^n) ≃ (Fin n → Fin d) :=
  Fintype.equivOfCardEq (by simp)

def reindexVectorComputes (n d : ℕ) (a : Fin n → Fin d) :
    Computes (vectorEncoding d) (vectorEncoding n) (fun v => v ∘ a) :=
  assembleComputes _ n _ (fun i => coordinateComputes d (a i))

def assignmentInput (D : ℕ) (vr vi : Fin d → ℚ) (a : Fin n → Fin d)
    (F : FixedField K n) : ℕ × (ℕ × ((Fin n → ℚ) × (Fin n → ℚ))) :=
  (D,inverseRecoveryPrecision F D,vr ∘ a,vi ∘ a)

abbrev inverseCandidateInputEncoding (d : ℕ) :=
  pairEncoding encodingNatBool (conjugatePointEncoding d)

def assignmentInputComputes (F : FixedField K n) (d : ℕ) (a : Fin n → Fin d) :
    Computes (inverseCandidateInputEncoding d) (inverseLatticeInputEncoding n)
      (fun p => assignmentInput p.1 p.2.1 p.2.2 a F) := by
  let D := Wiring.firstComputes encodingNatBool (conjugatePointEncoding d)
  let point := Wiring.secondComputes encodingNatBool (conjugatePointEncoding d)
  let vr := (point.andThen (Wiring.firstComputes (vectorEncoding d) (vectorEncoding d))).andThen
    (reindexVectorComputes n d a)
  let vi := (point.andThen (Wiring.secondComputes (vectorEncoding d) (vectorEncoding d))).andThen
    (reindexVectorComputes n d a)
  exact congrComputes (pairComputes D
    (pairComputes (D.andThen (inverseRecoveryPrecisionComputes F)) (pairComputes vr vi)))
    (fun _ => rfl)

def inverseCandidate (F : FixedField K n) (D : ℕ) (vr vi : Fin d → ℚ)
    (a : Fin n → Fin d) : Fin n → ℚ :=
  inverseLatticePoint F D (inverseRecoveryPrecision F D) (vr ∘ a) (vi ∘ a)

def inverseCandidateComputes (F : FixedField K n) (d : ℕ) (a : Fin n → Fin d) :
    Computes (inverseCandidateInputEncoding d) (vectorEncoding n)
      (fun p => inverseCandidate F p.1 p.2.1 p.2.2 a) :=
  congrComputes ((assignmentInputComputes F d a).andThen (inverseLatticePointComputes F))
    (fun _ => rfl)

theorem inverseCandidate_recovers (F : FixedField K n) (D : ℕ) (hD : 0 < D)
    (vr vi : Fin d → ℚ) (a : Fin n → Fin d) (x : K)
    (hx : IsIntegral ℤ ((D : K)*x))
    (hv : ∀ j, ‖rationalComplexPoint vr vi (a j)-conjugateValues F x j‖ ≤
      1/(2 : ℝ)^(inverseRecoveryPrecision F D)) :
    inverseCandidate F D vr vi a = fun i => F.basis.repr x i := by
  apply inverseLatticePoint_recovers F D hD _ _ _ x hx
    (1/(2 : ℝ)^(inverseRecoveryPrecision F D)) (by positivity)
  · exact hv
  · exact inverseRecoveryPrecision_accuracy F D hD

/-- A covering candidate array gives at least one successful finite assignment.
No property of its extra points, their order, or repetitions is required. -/
theorem inverseCandidate_exists (F : FixedField K n) (D : ℕ) (hD : 0 < D)
    (vr vi : Fin d → ℚ) (x : K) (hx : IsIntegral ℤ ((D : K)*x))
    (cover : ∀ i, ∃ j, ‖rationalComplexPoint vr vi j-conjugateValues F x i‖ ≤
      1/(2 : ℝ)^(inverseRecoveryPrecision F D)) :
    ∃ index : Fin (d^n), inverseCandidate F D vr vi (assignmentEnumeration n d index) =
      fun i => F.basis.repr x i := by
  choose a ha using cover
  refine ⟨(assignmentEnumeration n d).symm a,?_⟩
  rw [Equiv.apply_symm_apply]
  exact inverseCandidate_recovers F D hD vr vi a x hx ha

end
end Paper2.ExactInput.FixedRootCodec
