import Paper2.DegreeCSP.BinaryTractOrthogonality
import Paper2.Paper1ProvedComplexity
import Holant.Proofs.Hardness.ComplexPlaneThreeSupportSource
import Holant.Proofs.Hardness.EOBinaryPlaneFullSupportSource

/-! The literal opposite-pair lift of a non-BO binary signature has a proved
controlled counting source. The three-support and full-support machines are
the retained actual Paper 1 implementations; their original graph and field
answer encodings are preserved. -/
namespace Paper2.DegreeCSP.BinaryPlaneSource
open Computability Paper2.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (coefficient coefficient_algebraic field presentation targetEncoding targetValue target_value_exact)
end O

def lifted (g : Signature AlgebraicComplex 2) : Signature ℂ 4 :=
  fun x => (EOBinaryPlaneCore.lift (K:=AlgebraicComplex) g x : ℂ)

theorem lifted_algebraic (g : Signature AlgebraicComplex 2) (x : Fin 4 → Bool) :
    IsAlgebraic ℚ (lifted g x) :=
  (EOBinaryPlaneCore.lift g x).property.isAlgebraic

theorem lifted_plane (g : Signature AlgebraicComplex 2) :
    ComplexPlaneThreeSupportData.Plane (lifted g) := by
  refine ⟨0,?_,?_⟩ <;> simp [lifted,FiveSupportEOOrdering.middleCoeff,
    FiveSupportEOOrdering.middleWord,EOBinaryPlaneCore.lift]

theorem lifted_eo (g : Signature AlgebraicComplex 2) :
    DenseEOUnitLocal.EOSupport (lifted g) := by
  intro x hx
  exact congrArg Subtype.val (EOBinaryPlaneCore.lift_eo g x hx)

private theorem coe_lift (g : Signature AlgebraicComplex 2) :
    lifted g = EOBinaryPlaneCore.lift (fun x => (g x : ℂ)) := by
  funext x
  by_cases h : x 1=!(x 0) ∧ x 3=!(x 2) <;>
    simp [lifted,EOBinaryPlaneCore.lift,h]

theorem support_coe (g : Signature AlgebraicComplex 2) :
    ComplexPlaneThreeSupportData.support (fun x => (g x : ℂ)) =
      EOQuaternarySparseTract.support g := by
  classical
  ext x
  simp only [ComplexPlaneThreeSupportData.mem_support,
    EOQuaternarySparseTract.mem_support]
  exact_mod_cast Iff.rfl

theorem lifted_support (g : Signature AlgebraicComplex 2) :
    (ComplexPlaneThreeSupportData.support (lifted g)).card =
      (EOQuaternarySparseTract.support g).card := by
  rw [coe_lift,ComplexPlaneThreeSupportData.support_card_lift,support_coe]

theorem support_three_or_four (g : Signature AlgebraicComplex 2)
    (h : ¬OriginalBO.BlockOrthogonal (fun s t : Bool => (g ![s,t] : ℂ))) :
    (EOQuaternarySparseTract.support g).card = 3 ∨
      (EOQuaternarySparseTract.support g).card = 4 := by
  classical
  have hn := (BinaryTractOrthogonality.not_binary_tract_of_not_bo g h).2
  have hsmall : ¬(EOQuaternarySparseTract.support g).card ≤ 2 := by
    intro hs
    apply hn
    exact (Paper2.Paper1Proved.product_iff g).mpr
      (EOQuaternarySparseTract.binary_small g hs)
  have hup := Finset.card_le_card
    (Finset.subset_univ (EOQuaternarySparseTract.support g))
  have hc : (Finset.univ : Finset (Fin 2 → Bool)).card = 4 := by decide
  rw [hc] at hup
  omega

theorem lifted_nontract (g : Signature AlgebraicComplex 2)
    (h : ¬OriginalBO.BlockOrthogonal (fun s t : Bool => (g ![s,t] : ℂ))) :
    ¬Holant.Tractable.EOTract
      {⟨4,EOBinaryPlaneFullSupportData.algebraic (lifted g) (lifted_algebraic g)⟩} := by
  have he : EOBinaryPlaneFullSupportData.algebraic (lifted g) (lifted_algebraic g) =
      EOBinaryPlaneCore.lift g := by
    funext x
    apply Subtype.ext
    rfl
  rw [he]
  exact BinaryTractOrthogonality.lift_not_eoTract g h

variable {A : Type} {ea : Encoding A Bool} {count : A → ℕ}

/-- The unconditional finite-machine source on the exact lifted binary oracle.
No degree-CSP hardness callback or successful-output witness is an input. -/
def source (g : Signature AlgebraicComplex 2)
    (h : ¬OriginalBO.BlockOrthogonal (fun s t : Bool => (g ![s,t] : ℂ)))
    (w : Holant.Complexity.SharpPWitness ea count) :
    Holant.Complexity.LengthControlledOracleReduction ea encodingNatBool
      O.targetEncoding (O.presentation (lifted g) (lifted_algebraic g)).encoding
      count (O.targetValue (lifted g) (lifted_algebraic g)) := by
  classical
  by_cases h3 : (EOQuaternarySparseTract.support g).card = 3
  · exact ComplexPlaneThreeSupportSource.source (lifted g) (lifted_algebraic g)
      (lifted_plane g) (lifted_eo g) (by rw [ComplexPlaneThreeSupportData.ExactlyThree,lifted_support]; exact h3) w
  · have h4 := (support_three_or_four g h).resolve_left h3
    exact EOBinaryPlaneFullSupportSource.source (lifted g) (lifted_algebraic g)
      (lifted_plane g) (lifted_eo g)
      (by rw [EOBinaryPlaneFullSupportData.ExactlyFour,lifted_support]; exact h4)
      (lifted_nontract g h) w

end
end Paper2.DegreeCSP.BinaryPlaneSource
