import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticStatement
import Paper2.Certificates.DihedralSupport.AtlasRulingFactors
import Paper2.SourceFaithful.SourceStatements.OddDihedralCanonicalContractions
import Paper2.SourceFaithful.SourceStatements.OddDihedralRulingGeometry
import Paper2.SourceFaithful.SourceStatements.OddDihedralSupportStatement

/-! Proposition A.1 of the pinned manuscript, with its three clauses in one
public statement. Geometry is counted in the actual complex signature space;
the six-port hypothesis asks only for the fifteen unordered port pairs with
the residual ports in increasing order. Support cosets use the literal F₂
linear span of the indicators of arbitrary unordered even partitions. -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralSixPort
open Paper2.Certificates.DihedralSupport
open Paper2.HeightOne.Dihedral.SixPortSupport
open OddDihedralPencilExclusion OddDihedralSupport

/-- The source proposition, including the complete geometric counts,
the nonconstant-pencil restriction, and the exact support classification.
No classification, certificate, or stronger ordered-deck premise is
supplied by the caller. -/
structure SourceA1Packet (omega : ℂ) : Prop where
  atlas : ∀ epsilon : Bool, AtlasGeometrySemantic.AtlasStatement omega epsilon
  rulings : ∀ (l : AtlasCounts.RulingLabel) (v : AtlasVectors.Coordinate → ℂ),
    v ∈ Submodule.span ℂ
      ({AtlasVectors.vector omega (AtlasCounts.richPoints (.inr (.inl l)) 0),
        AtlasVectors.vector omega (AtlasCounts.richPoints (.inr (.inl l)) 1)} :
        Set (AtlasVectors.Coordinate → ℂ)) → AtlasRulingFactors.FixedRuling omega l v
  pencils : ∀ (eta : Bool) (f : Signature ℂ 6),
    (∀ x, f x ≠ 0 → Paper2.HeightOne.parity x = eta.toNat) →
    CanonicalAtlasContractions omega eta f → PencilStatement omega eta f
  supports : ∀ S : Support6, SupportStatement S

theorem source_A_1 (omega : ℂ) (hpoly : omega ^ 2 + omega + 1 = 0) :
    SourceA1Packet omega := by
  exact ⟨fun epsilon => AtlasGeometrySemantic.source_A_1_i omega hpoly epsilon,
    fun l v hv => AtlasRulingFactors.span_fixedRuling omega
      (CyclotomicComplex.cube_of_polynomial omega hpoly) l v hv,
    fun eta f hpar hf => source_A_1_ii_literal omega hpoly eta f hpar hf,
    fun S => source_A_1_iii S⟩

end Paper2.SourceFaithful.SourceStatements.OddDihedralSixPort

