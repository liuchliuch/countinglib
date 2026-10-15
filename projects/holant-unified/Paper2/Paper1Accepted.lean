import Paper2.Problem

/-!
# Explicit permitted Paper 1 inputs, with concrete Paper 2 semantics

Source: Liu–Meng, arXiv:2609.00219v1, the numbered results listed below.
This record is a transparent parameter; there is no inhabitant, axiom, or hidden
Paper 2 branch theorem. In particular it contains no charge bridge, mountain,
height-completeness, relative-EO, reconstruction or Bell-reduction assumption.
-/
namespace Paper2
open Tractable ExactInput

/-- Literal binary equality, not a proportional or merely accessible replacement. -/
def HasLiteralEquality (L : Language) : Prop :=
  (⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex) ∈ L.family

/-- Exact nontrivial ordered bipartition factorization. A scalar can be absorbed
in either factor; both positive arities rule out nullary scalar factorizations. -/
def TensorPrime {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  f ≠ 0 ∧ ∀ m k, 0 < m → 0 < k → ∀ e : Fin (m + k) ≃ Fin n,
    ∀ a : Signature AlgebraicComplex m, ∀ b : Signature AlgebraicComplex k,
      Tensor.reindex e (Signature.tensor a b) ≠ f

/-- The exact arity-four/even-parity/prime/two-endpoint hypothesis of Theorem 1.3. -/
def HasPrimeEightVertex (L : Language) : Prop :=
  ∃ f : Signature AlgebraicComplex 4,
    (⟨4, f⟩ : AnySignature AlgebraicComplex) ∈ L.family ∧ TensorPrime f ∧
      (∀ x, Odd (weight x) → f x = 0) ∧
      f (fun _ => false) * f (fun _ => true) ≠ 0

/-- The ordinary family denoted by applying the literal normalized K on every port. -/
noncomputable def kImage (L : Language) : SignatureFamily AlgebraicComplex :=
  familyAction sourceKBasis L.family

/-- Only exact named source results are accepted. Each conclusion refers to the
full structural criterion and to literal graph/root-code finite-machine semantics. -/
structure Paper1Accepted where
  /-- Paper 1 Theorem 2.22: effective recognition on finite exact algebraic tables. -/
  recognition_2_22 : Nonempty Problem.TractRecognizer
  /-- Paper 1 Theorem 2.22: fixed-family ordinary evaluation, including zero/nullary inputs. -/
  evaluation_2_22 : ∀ L : Language, Tract L.family → Problem.InFP .ordinary L
  /-- Paper 1 Theorem 1.2, preserving its reduced four-clause criterion. -/
  literalEquality_1_2 : ∀ L : Language, HasLiteralEquality L →
    (TractX (kImage L) → Problem.InFP .nativeX L) ∧
    (¬ TractX (kImage L) → Problem.SharpPHard .nativeX L)
  /-- The exact binary-Z-anchor specialization of Paper 1 Lemma 2.13.
  For the literal I-present native family, K⊗²I is Z in the ordinary family. -/
  equalityAnchor_2_13 : ∀ L : Language, HasLiteralEquality L →
    (Tract (kImage L) ↔ TractX (kImage L))
  /-- Paper 1 Theorem 1.3; no arbitrary quaternary or formal slice is admitted. -/
  primeQuaternary_1_3 : ∀ L : Language, HasPrimeEightVertex L →
    (Tract (kImage L) → Problem.InFP .nativeX L) ∧
    (¬ Tract (kImage L) → Problem.SharpPHard .nativeX L)

namespace Paper1Accepted

/-- Paper 2 Theorem 2.18, exactly the authorized Paper 1 import. -/
theorem recognitionAndEvaluation_2_18 (P : Paper1Accepted) :
    Nonempty Problem.TractRecognizer ∧
      ∀ L : Language, Tract L.family → Problem.InFP .ordinary L :=
  ⟨P.recognition_2_22, P.evaluation_2_22⟩

/-- Classification portion of Paper 2 Theorem 2.23, from the reduced source theorem
and its anchor bridge. Native-input recognition is not claimed by this wrapper. -/
theorem literalEqualityDichotomy_2_23 (P : Paper1Accepted) (L : Language)
    (h : HasLiteralEquality L) :
    (Tract (kImage L) → Problem.InFP .nativeX L) ∧
    (¬ Tract (kImage L) → Problem.SharpPHard .nativeX L) := by
  obtain ⟨easy, hard⟩ := P.literalEquality_1_2 L h
  exact ⟨fun ht => easy ((P.equalityAnchor_2_13 L h).mp ht),
    fun ht => hard (fun hx => ht ((P.equalityAnchor_2_13 L h).mpr hx))⟩

/-- Classification portion of Paper 2 Theorem 2.24. Its native-input recognition
clause is not included in this wrapper; no effective K-image conversion is claimed. -/
theorem primeQuaternaryDichotomy_2_24 (P : Paper1Accepted) (L : Language)
    (h : HasPrimeEightVertex L) :
    (Tract (kImage L) → Problem.InFP .nativeX L) ∧
    (¬ Tract (kImage L) → Problem.SharpPHard .nativeX L) := P.primeQuaternary_1_3 L h

end Paper1Accepted
end Paper2
