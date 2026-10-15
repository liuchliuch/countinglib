import Paper2.SourceFaithful.SourceStatements.OddDihedralPencilNonconstant
import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticTables
import Paper2.Certificates.DihedralSupport.AtlasPencilIndependence

/-! The consequent of Appendix A.1(ii). Every projectively nonconstant
three-phase contraction pencil lies on an actual one-block line or on an
actual fixed Segre ruling. The literal linear-independence hypothesis is
retained, and the complex endpoint permits arbitrary tensor coefficients. -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
open Paper2.HeightOne Paper2.HeightOne.Dihedral SixPortSupport SixPortPencils
open Paper2.Certificates.DihedralSupport AtlasCounts AtlasGeometrySemantic
noncomputable section
set_option maxRecDepth 4096

variable {K : Type} [Field K] [CharZero K]

theorem nonconstant_rich_type (omega : K) (hpoly : omega ^ 2 + omega + 1 = 0)
    (eta : Bool) (f : Signature K 6) (hpar : HasParity f)
    (hf : AtlasContractions omega eta f) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (hn : NonconstantPencil f p xi) :
    (∃ l : OneBlockLabel, ∃ sigma : Equiv.Perm (Fin 3),
      RichPencil omega eta f p xi (.inl l) sigma) ∨
    (∃ l : RulingLabel, ∃ sigma : Equiv.Perm (Fin 3),
      RichPencil omega eta f p xi (.inr (.inl l)) sigma) := by
  have h := CyclotomicComplex.primitive_of_polynomial omega hpoly
  obtain ⟨labels,scalars,hl,hs,he⟩ := labels_and_coefficients omega h eta f hf p xi hn
  have h01 : labels 0 ≠ labels 1 := hl.ne (by decide)
  have h02 : labels 0 ≠ labels 2 := hl.ne (by decide)
  have h12 : labels 1 ≠ labels 2 := hl.ne (by decide)
  obtain ⟨line,hline⟩ := table_zeroMinors_classify omega hpoly (eta ^^ xi)
    (labels 0) (labels 1) (labels 2) h01 h02 h12
    (labels_minor3_zero omega eta f p xi labels scalars hs he)
  obtain ⟨sigma,hsigma⟩ := rich_phase_assignment labels hl line hline
  have hpencil : RichPencil omega eta f p xi line sigma := by
    intro j
    exact ⟨scalars j,hs j,by simpa only [hsigma j] using he j⟩
  rcases line with l | l
  · exact Or.inl ⟨l,sigma,hpencil⟩
  · rcases l with l | l
    · exact Or.inr ⟨l,sigma,hpencil⟩
    · rcases l with l | l
      · exact (no_secant_rich_pencil omega h eta f hpar hf p xi l sigma hpencil).elim
      · exact (no_triangle_rich_pencil omega h eta f hpar hf p xi l sigma hpencil).elim

/-- The literal source nonconstancy condition, with no supplied coordinate
minor, atlas representatives, line certificate, or phase assignment. -/
theorem source_A_1_ii_consequence (omega : K) (hpoly : omega ^ 2 + omega + 1 = 0)
    (eta : Bool) (f : Signature K 6)
    (hpar : ∀ x, f x ≠ 0 → parity x = eta.toNat)
    (hf : AtlasContractions omega eta f) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (hn : LinearIndependent K ![first f p xi,second f p xi]) :
    (∃ l : OneBlockLabel, ∃ sigma : Equiv.Perm (Fin 3),
      RichPencil omega eta f p xi (.inl l) sigma) ∨
    (∃ l : RulingLabel, ∃ sigma : Equiv.Perm (Fin 3),
      RichPencil omega eta f p xi (.inr (.inl l)) sigma) := by
  exact nonconstant_rich_type omega hpoly eta f
    (fun x y hx hy => (hpar x hx).trans (hpar y hy).symm) hf p xi
    ((AtlasPencils.pairIndependent_iff_minor _ _).mp hn)

/-- Appendix A.1(ii), including its one-block-or-ruling consequent, on
arbitrary complex tensors. -/
theorem source_A_1_ii_consequence_complex (omega : ℂ) (hpoly : omega ^ 2 + omega + 1 = 0)
    (eta : Bool) (f : Signature ℂ 6)
    (hpar : ∀ x, f x ≠ 0 → parity x = eta.toNat)
    (hf : AtlasContractions omega eta f) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (hn : LinearIndependent ℂ ![first f p xi,second f p xi]) :
    (∃ l : OneBlockLabel, ∃ sigma : Equiv.Perm (Fin 3),
      RichPencil omega eta f p xi (.inl l) sigma) ∨
    (∃ l : RulingLabel, ∃ sigma : Equiv.Perm (Fin 3),
      RichPencil omega eta f p xi (.inr (.inl l)) sigma) :=
  source_A_1_ii_consequence omega hpoly eta f hpar hf p xi hn

end
end Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion

