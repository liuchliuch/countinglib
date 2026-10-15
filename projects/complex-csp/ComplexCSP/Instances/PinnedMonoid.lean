import ComplexCSP.Instances.PresentationAlgorithms
import ComplexCSP.Structure.TensorCharacters
import ComplexCSP.Structure.CharacterIndependence
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Characters of the actual generated-table monoid

This is the semantic monoid of generated pinned tables, not a claim that literal
instance gluing is strictly associative. Closure is witnessed by actual finite
instances. Every monoid element has a finite presentation, and every finite
presentation maps into the monoid. Thus universal identities on this semantic
monoid are equivalent to universal identities on the generated family.
-/

namespace ComplexCSP

open scoped BigOperators

section Basic

variable {D K ι B : Type} [CommSemiring K] [Fintype D]

/-- Actual generated pinned tables form a submonoid under pointwise product. -/
def generatedTableSubmonoid (L : Language D K ι) (B : Type) :
    Submonoid ((B → D) → K) where
  carrier := {G | Instance.Generated L G}
  one_mem' := Instance.generated_one
  mul_mem' := fun hG hF => Instance.generated_mul hG hF

/-- The semantic monoid of tables admitting literal finite CSP presentations. -/
abbrev GeneratedTable (L : Language D K ι) (B : Type) := generatedTableSubmonoid L B

namespace GeneratedTable

variable {L : Language D K ι}

/-- Interpret a finite presentation in the semantic generated-table monoid. -/
def ofPresentation (P : Presentation L B) : GeneratedTable L B :=
  ⟨P.table, P.table_generated⟩

@[simp] theorem ofPresentation_apply (P : Presentation L B) (a : B → D) :
    (ofPresentation P).val a = P.table a := rfl

/-- No extra functions were added: each semantic monoid element is presented
by a finite instance with canonically encoded hidden variables. -/
theorem exists_presentation (G : GeneratedTable L B) :
    ∃ P : Presentation L B, ofPresentation P = G := by
  obtain ⟨n, I, hI⟩ := G.property
  refine ⟨⟨n, I⟩, Subtype.ext ?_⟩
  exact funext hI

/-- The presentation compiler's actual gluing realizes monoid multiplication. -/
@[simp] theorem ofPresentation_mul (P Q : Presentation L B) :
    ofPresentation (P.mul Q) = ofPresentation P * ofPresentation Q := by
  apply Subtype.ext
  funext a
  exact Presentation.table_mul P Q a

@[simp] theorem ofPresentation_one :
    ofPresentation (Presentation.one : Presentation L B) = 1 := by
  apply Subtype.ext
  funext a
  exact Presentation.table_one (L := L) a

/-- Universal assertions on this monoid are exactly universal assertions on
actual finite presentations. This applies to arbitrary predicates of tables. -/
theorem forall_iff_presentations (Q : ((B → D) → K) → Prop) :
    (∀ G : GeneratedTable L B, Q G.val) ↔ ∀ P : Presentation L B, Q P.table := by
  constructor
  · intro h P
    exact h (ofPresentation P)
  · intro h G
    obtain ⟨P, rfl⟩ := exists_presentation G
    exact h P

/-- Universal assertions on presentations are exactly assertions on every
literal instance with a canonical finite hidden-variable type. -/
theorem forall_presentations_iff_instances (Q : ((B → D) → K) → Prop) :
    (∀ P : Presentation L B, Q P.table) ↔
      ∀ n : ℕ, ∀ I : Instance L B (Fin n), Q I.partition := by
  constructor
  · intro h n I
    exact h ⟨n, I⟩
  · rintro h ⟨n, I⟩
    exact h n I

end GeneratedTable

/-- Evaluation at a boundary pin is a genuine unital multiplicative character. -/
def pinnedCharacter (L : Language D K ι) (a : B → D) : GeneratedTable L B →* K where
  toFun G := G.val a
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem pinnedCharacter_ofPresentation (L : Language D K ι)
    (a : B → D) (P : Presentation L B) :
    pinnedCharacter L a (GeneratedTable.ofPresentation P) = P.table a := rfl

section Star

variable [StarRing K]

/-- The conjugate pinned coordinate is also a genuine monoid character. -/
def conjugatePinnedCharacter (L : Language D K ι) (a : B → D) :
    GeneratedTable L B →* K :=
  (starRingEnd K).toMonoidHom.comp (pinnedCharacter L a)

@[simp] theorem conjugatePinnedCharacter_apply (L : Language D K ι)
    (a : B → D) (G : GeneratedTable L B) :
    conjugatePinnedCharacter L a G = star (G.val a) := rfl

/-- The monomial character with `p` direct factors and `q` conjugate factors. -/
def pinnedMonomialCharacter (L : Language D K ι) {p q : ℕ}
    (a : Fin p → B → D) (b : Fin q → B → D) : GeneratedTable L B →* K :=
  (∏ j, pinnedCharacter L (a j)) * ∏ j, conjugatePinnedCharacter L (b j)

@[simp] theorem pinnedMonomialCharacter_apply (L : Language D K ι) {p q : ℕ}
    (a : Fin p → B → D) (b : Fin q → B → D) (G : GeneratedTable L B) :
    pinnedMonomialCharacter L a b G =
      (∏ j, G.val (a j)) * ∏ j, star (G.val (b j)) := by
  simp [pinnedMonomialCharacter, pinnedCharacter]

/-- The actual tensorized constraint instance realizes the monomial character. -/
theorem tensor_realizes_pinnedMonomial (L : Language D K ι) (P : Presentation L B)
    (p q : ℕ) (a : Fin p → B → D) (b : Fin q → B → D) :
    (P.inst.tensorConjugate p q).partition (tensorPins a b) =
      pinnedMonomialCharacter L a b (GeneratedTable.ofPresentation P) := by
  rw [Instance.partition_tensorConjugate, pinnedMonomialCharacter_apply]
  rfl

/-- The independent formal coordinate variables of the paper: a direct copy
and a conjugate copy of every boundary pin. -/
abbrev PinnedCoordinate (B D : Type) := (B → D) ⊕ (B → D)

/-- Every formal coordinate is interpreted as a genuine monoid character. -/
def pinnedCoordinateCharacter (L : Language D K ι) :
    PinnedCoordinate B D → GeneratedTable L B →* K :=
  Sum.elim (pinnedCharacter L) (conjugatePinnedCharacter L)

@[simp] theorem pinnedCoordinateCharacter_apply (L : Language D K ι)
    (v : PinnedCoordinate B D) (G : GeneratedTable L B) :
    pinnedCoordinateCharacter L v G =
      Sum.elim G.val (fun a => star (G.val a)) v := by
  cases v <;> rfl

/-- A finitely supported exponent vector gives a monomial character by actual
finite multiplication of the pinned-coordinate characters. -/
def pinnedExponentCharacter (L : Language D K ι)
    (d : PinnedCoordinate B D →₀ ℕ) : GeneratedTable L B →* K :=
  ∏ v ∈ d.support, (pinnedCoordinateCharacter L v) ^ d v

@[simp] theorem pinnedExponentCharacter_apply (L : Language D K ι)
    (d : PinnedCoordinate B D →₀ ℕ) (G : GeneratedTable L B) :
    pinnedExponentCharacter L d G =
      ∏ v ∈ d.support, (Sum.elim G.val (fun a => star (G.val a)) v) ^ d v := by
  simp [pinnedExponentCharacter]

/-- Expanding an actual formal polynomial gives the finite character expression
used in the universal identity proof. The direct/conjugate variables remain
formally independent; conjugation enters only at evaluation. -/
theorem polynomial_eval_as_characters (L : Language D K ι)
    (p : MvPolynomial (PinnedCoordinate B D) K) (G : GeneratedTable L B) :
    MvPolynomial.eval (Sum.elim G.val (fun a => star (G.val a))) p =
      ∑ d ∈ p.support, p.coeff d * pinnedExponentCharacter L d G := by
  simp only [MvPolynomial.eval_eq, pinnedExponentCharacter_apply]

end Star

end Basic

section PolynomialIdentities

variable {D K ι B : Type} [Field K] [StarRing K] [DecidableEq K] [Fintype D]

/-- The verified finite grouping test is equivalent to the universal polynomial
identity over all actual finite presentations. The finite comparison matrix is
an explicit input with its soundness/completeness contract; no implementation
of the paper's pinned-isomorphism comparison theorem is assumed or claimed. -/
theorem polynomial_identity_test_correct (L : Language D K ι)
    (p : MvPolynomial (PinnedCoordinate B D) K)
    (same : (PinnedCoordinate B D →₀ ℕ) → (PinnedCoordinate B D →₀ ℕ) → Bool)
    (hsame : ∀ d ∈ p.support, ∀ e ∈ p.support,
      same d e = true ↔ pinnedExponentCharacter L d = pinnedExponentCharacter L e) :
    indexedCharacterZeroTest p.support same p.coeff = true ↔
      ∀ P : Presentation L B,
        MvPolynomial.eval (Sum.elim P.table (fun a => star (P.table a))) p = 0 := by
  rw [indexedCharacterZeroTest_correct p.support (pinnedExponentCharacter L) same p.coeff hsame]
  simp_rw [← polynomial_eval_as_characters]
  exact GeneratedTable.forall_iff_presentations (L := L)
    (fun G => MvPolynomial.eval (Sum.elim G (fun a => star (G a))) p = 0)

/-- The same test detects precisely a counterexample realized by a finite
presentation. This proves existence, not an effective counterexample bound. -/
theorem polynomial_identity_test_rejects_iff (L : Language D K ι)
    (p : MvPolynomial (PinnedCoordinate B D) K)
    (same : (PinnedCoordinate B D →₀ ℕ) → (PinnedCoordinate B D →₀ ℕ) → Bool)
    (hsame : ∀ d ∈ p.support, ∀ e ∈ p.support,
      same d e = true ↔ pinnedExponentCharacter L d = pinnedExponentCharacter L e) :
    indexedCharacterZeroTest p.support same p.coeff = false ↔
      ∃ P : Presentation L B,
        MvPolynomial.eval (Sum.elim P.table (fun a => star (P.table a))) p ≠ 0 := by
  classical
  rw [← Bool.not_eq_true, polynomial_identity_test_correct L p same hsame]
  push_neg
  rfl

end PolynomialIdentities

end ComplexCSP
