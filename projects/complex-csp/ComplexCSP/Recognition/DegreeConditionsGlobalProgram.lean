import ComplexCSP.Recognition.DegreeConditionsCompression
import ComplexCSP.Recognition.DegreeConditionsTransport
import ComplexCSP.Structure.DegreeStructuralCollapse
import ComplexCSP.Recognition.GlobalCorrectness

/-! # Exact recognition: finite degree-restricted global certificate program

The program invokes the proved cyclic-filter identity algorithm on each actual
finite certificate equation. Its semantic theorem quantifies only literal
degree-divisible presentations, through exact coefficient transport and
proved degree-preserving external-arity compression.
-/
namespace ComplexCSP.Recognition
open Certificates PolynomialPrograms
variable {D K R ι : Type}
variable [Field K] [StarRing K] [CharZero K] [DecidableEq K]
variable [Fintype D] [DecidableEq D] [Encodable D] [Fintype ι]
variable [Fintype R] [Encodable R]

/-- The actual degree-filtered identity test at one external arity. -/
def degreeArityCertificateTest (L : Language D K ι) (δ : ℕ) (ζ : K)
    (roots : RootAlphabet K R) (r : ℕ) : Bool :=
  (optimizedProductPrograms (matrixCoordinateIndex (D := D) r) roots).all
    (degreeProgramIdentityTest L δ ζ (matrixCoordinates r))

theorem degreeArityCertificateTest_correct (L : Language D K ι)
    {δ : ℕ} {ζ : K} (hδ : 0 < δ) (hζ : IsPrimitiveRoot ζ δ)
    (roots : RootAlphabet K R) (r : ℕ) :
    degreeArityCertificateTest L δ ζ roots r = true ↔
      ∀ Q : Presentation L (Fin (r + 1)), Q.DegreeDivisible δ →
        ∃ c : Certificate (Fin r → D) D R, c.Retained roots ∧
          Satisfies roots c (fun x z => Q.table (Fin.snoc x z)) := by
  rw [degreeArityCertificateTest,List.all_eq_true]
  constructor
  · intro h Q hQ
    apply (optimizedProductPrograms_zero_iff (matrixCoordinateIndex r) roots
      (fun x z => Q.table (Fin.snoc x z))).mp
    intro P hP
    exact (degreeProgramIdentityTest_correct L hδ hζ (matrixCoordinates r) P).mp
      (h P hP) Q hQ
  · intro h P hP
    apply (degreeProgramIdentityTest_correct L hδ hζ (matrixCoordinates r) P).mpr
    intro Q hQ
    exact (optimizedProductPrograms_zero_iff (matrixCoordinateIndex r) roots
      (fun x z => Q.table (Fin.snoc x z))).mpr (h Q hQ) P hP

/-- A finite external-arity loop; hidden variables and instance sizes remain unbounded. -/
def degreeGlobalCertificateTest (L : Language D K ι) (δ : ℕ) (ζ : K)
    (roots : RootAlphabet K R) : Bool :=
  (List.range (Fintype.card D ^ 2 + 1)).all
    (fun r => if r = 0 then true else degreeArityCertificateTest L δ ζ roots r)

theorem degreeGlobalCertificateTest_correct (L : Language D K ι)
    {δ : ℕ} {ζ : K} (hδ : 0 < δ) (hζ : IsPrimitiveRoot ζ δ)
    (roots : RootAlphabet K R) :
    degreeGlobalCertificateTest L δ ζ roots = true ↔
      ∀ r : ℕ, 0 < r → r + 1 ≤ Fintype.card D ^ 2 + 1 →
        ∀ Q : Presentation L (Fin (r + 1)), Q.DegreeDivisible δ →
          ∃ c : Certificate (Fin r → D) D R, c.Retained roots ∧
            Satisfies roots c (fun x z => Q.table (Fin.snoc x z)) := by
  simp only [degreeGlobalCertificateTest,List.all_eq_true,List.mem_range]
  constructor
  · intro h r hr hb
    have ht := h r (by omega)
    simp only [Nat.ne_of_gt hr,if_false] at ht
    exact (degreeArityCertificateTest_correct L hδ hζ roots r).mp ht
  · intro h r hr
    by_cases hz : r = 0
    · simp [hz]
    · simp only [hz,if_false]
      exact (degreeArityCertificateTest_correct L hδ hζ roots r).mpr
        (h r (Nat.pos_of_ne_zero hz) (by omega))

section GlobalCorrectness
variable [NumberField K] [Nonempty D]
variable (E : ℕ) [Fintype (rootsOfUnity E K)] [Encodable (rootsOfUnity E K)]
    (hE : 0 < E) (hkill : RowDetector.KillsTorsion K E)
include hE hkill

/-- Actual joint legal BO of the degree-generated family, with a proved primitive
filter root and a proved complete runtime torsion exponent. -/
theorem degreeGlobalCertificateTest_exponent_correct_jointBO
    (L : Language D K ι) {δ : ℕ} {ζ : K}
    (hδ : 0 < δ) (hζ : IsPrimitiveRoot ζ δ) (σ : K →+* ℂ) :
    degreeGlobalCertificateTest L δ ζ (exponentRootAlphabet K E) = true ↔
      DegreeJointBO (L.mapValues σ) δ := by
  rw [degreeGlobalCertificateTest_correct L hδ hζ, degreeJointBO_iff_bounded]
  constructor
  · intro h T hT hpos hbound
    obtain ⟨P,hP,hT⟩ := hT
    let Q : Presentation L (Fin (T.rowArity + 1)) := ⟨P.hidden,P.inst.sourceValues σ⟩
    have hQ : Q.DegreeDivisible δ :=
      (Instance.degreeDivisible_sourceValues_iff σ P.inst δ).mpr hP
    have hv (a : Fin (T.rowArity + 1) → D) : σ (Q.table a) = T.value a := by
      change σ ((P.inst.sourceValues σ).partition a) = T.value a
      rw [Instance.partition_sourceValues]
      exact congrFun hT a
    have hb := (embedded_singleton_iff_exponent_certificate E hE hkill σ Q.table).mpr
      (h T.rowArity hpos hbound Q hQ)
    have ht : PositiveTable.mk T.rowArity (fun a => σ (Q.table a)) = T := by
      cases T
      congr 1
      exact funext hv
    rwa [ht] at hb
  · intro h r hr hb Q hQ
    let T : PositiveTable D := ⟨r,fun a => σ (Q.table a)⟩
    have hT : DegreeGenerated (L.mapValues σ) δ T.value :=
      DegreeGenerated.mapValues ⟨Q,hQ,rfl⟩ σ
    exact (embedded_singleton_iff_exponent_certificate E hE hkill σ Q.table).mp
      (h T hT hr hb)

/-- The three degree-multiple conditions have the same finite program decision. -/
theorem degreeGlobalCertificateTest_exponent_correct_conditions
    (L : Language D K ι) {δ : ℕ} {ζ : K}
    (hδ : 0 < δ) (hζ : IsPrimitiveRoot ζ δ) (σ : K →+* ℂ) :
    degreeGlobalCertificateTest L δ ζ (exponentRootAlphabet K E) = true ↔
      DegreeCaiChenConditions (L.mapValues σ) δ :=
  (degreeGlobalCertificateTest_exponent_correct_jointBO E hE hkill L hδ hζ σ).trans
    (degree_structural_collapse (L.mapValues σ) δ (mapped_language_algebraic L σ)).symm
end GlobalCorrectness
end ComplexCSP.Recognition
