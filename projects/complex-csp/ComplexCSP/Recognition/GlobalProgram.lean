import ComplexCSP.Recognition.CertificatePrograms
import ComplexCSP.Recognition.IdentityOracle

/-! # Finite global certificate testing

The program enumerates certificate branches, compiles their product identities,
and runs the exact identity oracle. The algebraic-input frontends construct the
coefficient arithmetic and root alphabet used here. -/
namespace ComplexCSP.Recognition
open Certificates PolynomialPrograms

variable {D K R ι : Type}
variable [Field K] [StarRing K] [CharZero K] [DecidableEq K]
variable [Fintype D] [DecidableEq D] [Encodable D] [Fintype ι]
variable [Fintype R] [Encodable R]

/-- A computable coordinate numbering derived from the supplied finite encodings. -/
def matrixCoordinateIndex (r : ℕ) :
    ((Fin r → D) × D) ≃ Fin (Fintype.card ((Fin r → D) × D)) :=
  Encodable.fintypeEquivFin

/-- Each matrix entry is the corresponding direct pinned coordinate of the
(r+1)-ary original table. No conjugation is silently substituted. -/
def matrixCoordinates (r : ℕ) :
    Fin (Fintype.card ((Fin r → D) × D)) → PinnedCoordinate (Fin (r + 1)) D :=
  fun i => Sum.inl (Fin.snoc ((matrixCoordinateIndex r).symm i).1
    ((matrixCoordinateIndex r).symm i).2)

/-- Exact finite test for all generated tables at one external arity. -/
def arityCertificateTest (L : Language D K ι) (roots : RootAlphabet K R) (r : ℕ) : Bool :=
  (optimizedProductPrograms (matrixCoordinateIndex (D := D) r) roots).all
    (programIdentityTest L (matrixCoordinates r))

/-- The program decides universal membership in the actual finite certificate
union. The character-comparison matrix is computed internally by finite target
isomorphism tests, not supplied as an assumption. -/
theorem arityCertificateTest_correct (L : Language D K ι)
    (roots : RootAlphabet K R) (r : ℕ) :
    arityCertificateTest L roots r = true ↔
      ∀ Q : Presentation L (Fin (r + 1)),
        ∃ c : Certificate (Fin r → D) D R, c.Retained roots ∧
          Satisfies roots c (fun x z => Q.table (Fin.snoc x z)) := by
  rw [arityCertificateTest,List.all_eq_true]
  constructor
  · intro h Q
    apply (optimizedProductPrograms_zero_iff (matrixCoordinateIndex r) roots
      (fun x z => Q.table (Fin.snoc x z))).mp
    intro P hP
    have hz := (programIdentityTest_correct L (matrixCoordinates r) P).mp (h P hP) Q
    exact hz
  · intro h P hP
    apply (programIdentityTest_correct L (matrixCoordinates r) P).mpr
    intro Q
    exact (optimizedProductPrograms_zero_iff (matrixCoordinateIndex r) roots
      (fun x z => Q.table (Fin.snoc x z))).mpr (h Q) P hP

/-- The source's finite external-arity range: row arities 1,...,|D|².
Hidden-variable counts remain unbounded inside the identity oracle. -/
def globalCertificateTest (L : Language D K ι) (roots : RootAlphabet K R) : Bool :=
  (List.range (Fintype.card D ^ 2 + 1)).all
    (fun r => if r = 0 then true else arityCertificateTest L roots r)

/-- Exact finite-loop correctness, with no bound claimed on presenting instances. -/
theorem globalCertificateTest_correct (L : Language D K ι) (roots : RootAlphabet K R) :
    globalCertificateTest L roots = true ↔
      ∀ r : ℕ, 0 < r → r + 1 ≤ Fintype.card D ^ 2 + 1 →
        ∀ Q : Presentation L (Fin (r + 1)),
          ∃ c : Certificate (Fin r → D) D R, c.Retained roots ∧
            Satisfies roots c (fun x z => Q.table (Fin.snoc x z)) := by
  simp only [globalCertificateTest,List.all_eq_true,List.mem_range]
  constructor
  · intro h r hr hb
    have htest := h r (by omega)
    simp only [Nat.ne_of_gt hr,if_false] at htest
    exact (arityCertificateTest_correct L roots r).mp htest
  · intro h r hr
    by_cases hz : r = 0
    · simp [hz]
    · simp only [hz,if_false]
      apply (arityCertificateTest_correct L roots r).mpr
      exact h r (Nat.pos_of_ne_zero hz) (by omega)

end ComplexCSP.Recognition
