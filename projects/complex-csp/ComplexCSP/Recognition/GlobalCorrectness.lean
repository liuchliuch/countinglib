import ComplexCSP.Recognition.GlobalProgram
import ComplexCSP.Recognition.CertificatesEmbeddingLift
import ComplexCSP.Recognition.CertificatesExponentRoots
import ComplexCSP.Structure.BoundedArity
import ComplexCSP.Structure.StructuralCollapse
import ComplexCSP.Instances.ValueTransport

/-! # From finite certificates to global Block Orthogonality

Source-field instances connect the finite arity, certificate, and identity tests
to every generated complex table. The algebraic-input frontends supply effective
field and root representations. -/
namespace ComplexCSP.Recognition
open Certificates BlockOrthogonality GeneratingSet

variable {D K ι : Type} [Field K] [NumberField K]
variable [Fintype D] [DecidableEq D]

/-- The actual singleton-purified BO locus under an arbitrary field embedding. -/
theorem embedded_singleton_iff_certificate (σ : K →+* ℂ) {r : ℕ}
    (G : (Fin (r + 1) → D) → K) :
    BlockOrthogonal (PositiveTable.mk r (fun a => σ (G a))).singletonRows ↔
      ∃ c : Certificate (Fin r → D) D (NumberFieldRoots K),
        c.Retained (numberFieldRootAlphabet K) ∧
          Satisfies (numberFieldRootAlphabet K) c (fun x z => G (Fin.snoc x z)) := by
  let T : PositiveTable D := ⟨r,fun a => σ (G a)⟩
  let P := LegalGeneratingSet.choose T.nonzeroValues
  have hc : LegalGeneratingSet.ContainsTable T.nonzeroValues
      (fun x z => σ (G (Fin.snoc x z))) := by
    intro x z hz
    exact (T.mem_nonzeroValues _).mpr ⟨x,z,rfl⟩
  exact embedded_legal_blockOrthogonal_iff_certificate σ P
    (fun x z => G (Fin.snoc x z)) hc

variable [Nonempty D] [Encodable D] [Fintype ι]
variable [StarRing K] [DecidableEq K] [Encodable (NumberFieldRoots K)]

/-- The computed program accepts exactly the actual original joint BO condition
of the embedded language. No universal-identity or comparison oracle is assumed. -/
theorem globalCertificateTest_correct_jointBO (L : Language D K ι) (σ : K →+* ℂ) :
    globalCertificateTest L (numberFieldRootAlphabet K) = true ↔ JointBO (L.mapValues σ) := by
  rw [globalCertificateTest_correct,jointBO_iff_bounded]
  constructor
  · intro h T hT hpos hbound
    obtain ⟨k,I,hI⟩ := hT
    let Q : Presentation L (Fin (T.rowArity + 1)) := ⟨k,I.sourceValues σ⟩
    have hv (a : Fin (T.rowArity + 1) → D) : σ (Q.table a) = T.value a := by
      change σ ((I.sourceValues σ).partition a) = T.value a
      rw [Instance.partition_sourceValues,hI]
    have hc := h T.rowArity hpos hbound Q
    have hb := (embedded_singleton_iff_certificate σ Q.table).mpr hc
    have ht : (PositiveTable.mk T.rowArity (fun a => σ (Q.table a))) = T := by
      cases T
      congr 1
      exact funext hv
    rwa [ht] at hb
  · intro h r hr hb Q
    let T : PositiveTable D := ⟨r,fun a => σ (Q.table a)⟩
    have hT : Instance.Generated (L.mapValues σ) T.value :=
      Instance.generated_mapValues Q.table_generated σ
    exact (embedded_singleton_iff_certificate σ Q.table).mp (h T hT hr hb)

/-- Algebraicity of every embedded input value is derived from its actual number
field, not separately assumed for the global correctness theorem. -/
theorem mapped_language_algebraic {A F s : Type} [Field F] [NumberField F]
    (L : Language A F s) (σ : F →+* ℂ) :
    ∀ i a, IsAlgebraic ℚ ((L.mapValues σ).value i a) := by
  intro i a
  exact (IsIntegral.map σ.toRatAlgHom (IsIntegral.of_finite ℚ (L.value i a))).isAlgebraic

/-- Three-condition correctness for the ordinary fixed root alphabet. -/
theorem globalCertificateTest_correct_conditions (L : Language D K ι) (σ : K →+* ℂ) :
    globalCertificateTest L (numberFieldRootAlphabet K) = true ↔
      CaiChenConditions (L.mapValues σ) :=
  (globalCertificateTest_correct_jointBO L σ).trans
    (structural_collapse (L.mapValues σ) (mapped_language_algebraic L σ)).symm

section RuntimeExponent
variable (E : ℕ) [Fintype (rootsOfUnity E K)] [Encodable (rootsOfUnity E K)]
variable (hE : 0 < E) (hkill : RowDetector.KillsTorsion K E)
include hE hkill
omit [Encodable (NumberFieldRoots K)]

omit [Nonempty D] [Encodable D] [StarRing K] [DecidableEq K]
  [Fintype (rootsOfUnity E K)] [Encodable (rootsOfUnity E K)] in
/-- Singleton semantics for the caller's proved runtime torsion exponent. -/
theorem embedded_singleton_iff_exponent_certificate (σ : K →+* ℂ) {r : ℕ}
    (G : (Fin (r + 1) → D) → K) :
    BlockOrthogonal (PositiveTable.mk r (fun a => σ (G a))).singletonRows ↔
      ∃ c : Certificate (Fin r → D) D (rootsOfUnity E K),
        c.Retained (exponentRootAlphabet K E) ∧
          Satisfies (exponentRootAlphabet K E) c (fun x z => G (Fin.snoc x z)) := by
  let T : PositiveTable D := ⟨r,fun a => σ (G a)⟩
  let P := LegalGeneratingSet.choose T.nonzeroValues
  have hc : LegalGeneratingSet.ContainsTable T.nonzeroValues
      (fun x z => σ (G (Fin.snoc x z))) := by
    intro x z hz
    exact (T.mem_nonzeroValues _).mpr ⟨x,z,rfl⟩
  exact embedded_legal_blockOrthogonal_iff_exponent_certificate σ P
    (fun x z => G (Fin.snoc x z)) hc E hE hkill

/-- Complete global program correctness with an actually computed exponent and
root enumeration available to instantiate the finite types. -/
theorem globalCertificateTest_exponent_correct_jointBO (L : Language D K ι) (σ : K →+* ℂ) :
    globalCertificateTest L (exponentRootAlphabet K E) = true ↔ JointBO (L.mapValues σ) := by
  rw [globalCertificateTest_correct,jointBO_iff_bounded]
  constructor
  · intro h T hT hpos hbound
    obtain ⟨k,I,hI⟩ := hT
    let Q : Presentation L (Fin (T.rowArity + 1)) := ⟨k,I.sourceValues σ⟩
    have hv (a : Fin (T.rowArity + 1) → D) : σ (Q.table a) = T.value a := by
      change σ ((I.sourceValues σ).partition a) = T.value a
      rw [Instance.partition_sourceValues,hI]
    have hb := (embedded_singleton_iff_exponent_certificate E hE hkill σ Q.table).mpr
      (h T.rowArity hpos hbound Q)
    have ht : (PositiveTable.mk T.rowArity (fun a => σ (Q.table a))) = T := by
      cases T
      congr 1
      exact funext hv
    rwa [ht] at hb
  · intro h r hr hb Q
    let T : PositiveTable D := ⟨r,fun a => σ (Q.table a)⟩
    have hT : Instance.Generated (L.mapValues σ) T.value :=
      Instance.generated_mapValues Q.table_generated σ
    exact (embedded_singleton_iff_exponent_certificate E hE hkill σ Q.table).mp (h T hT hr hb)

/-- The three source tractability conditions, for the actual embedded unbounded
family, are exactly what the runtime-exponent program tests. Input construction
and representation conversion remain separately stated implementation obligations. -/
theorem globalCertificateTest_exponent_correct_conditions (L : Language D K ι) (σ : K →+* ℂ) :
    globalCertificateTest L (exponentRootAlphabet K E) = true ↔
      CaiChenConditions (L.mapValues σ) :=
  (globalCertificateTest_exponent_correct_jointBO E hE hkill L σ).trans
    (structural_collapse (L.mapValues σ) (mapped_language_algebraic L σ)).symm

end RuntimeExponent

end ComplexCSP.Recognition
