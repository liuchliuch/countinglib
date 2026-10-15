import Paper2.SourceFaithful.SourceStatements.OddDihedralPencilStatement
import Paper2.Certificates.DihedralSupport.Semantics

/-! The literal fifteen increasing-order selected pairs of Appendix A.1.
Residual ports have their original increasing order. Pair reversal uses a
genuine inverse cube-root phase and retains its nonzero scalar. -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
open Paper2.HeightOne Paper2.HeightOne.Dihedral
open Paper2.Certificates.DihedralSupport
noncomputable section
set_option maxRecDepth 4096

variable {K : Type} [Field K]

def canonicalPencil (f : Signature K 6) (q : Fin 15) (xi : Bool) (s : K) : Signature K 4 :=
  fun r => f (liftWord q xi false r) - s * f (liftWord q xi true r)

/-- This is exactly the source's fifteen unordered selected pairs, with
residual coordinates in increasing port order. -/
def CanonicalAtlasContractions (omega : K) (eta : Bool) (f : Signature K 6) : Prop :=
  ∀ q xi (j : Fin 3), AtlasParityFrame.Admissible omega (eta ^^ xi)
    (canonicalPencil f q xi (omega ^ j.val))

theorem admissible_smul (omega : K) (epsilon : Bool) (f : Signature K 4)
    (hf : AtlasParityFrame.Admissible omega epsilon f) (c : K) :
    AtlasParityFrame.Admissible omega epsilon (c • f) := by
  by_cases hc : c = 0
  · left
    simp [hc]
  rcases hf with rfl | ⟨l,d,hd,rfl⟩
  · left
    simp
  · exact Or.inr ⟨l,c*d,mul_ne_zero hc hd,by rw [smul_smul]⟩

theorem canonical_admissible_root [CharZero K] (omega : K)
    (hpoly : omega ^ 2 + omega + 1 = 0) (eta : Bool) (f : Signature K 6)
    (hf : CanonicalAtlasContractions omega eta f) (q : Fin 15) (xi : Bool)
    (s : K) (hs : s ^ 3 = 1) :
    AtlasParityFrame.Admissible omega (eta ^^ xi) (canonicalPencil f q xi s) := by
  obtain ⟨j,rfl⟩ := CyclotomicComplex.cube_roots_complete omega hpoly s hs
  exact hf q xi j

theorem canonical_pencil_reversed (f : Signature K 6) (q : Fin 15) (xi : Bool)
    (s : K) (hs : s ≠ 0) :
    (fun r => f (liftWord q xi true r) - s * f (liftWord q xi false r)) =
      (-s) • canonicalPencil f q xi s⁻¹ := by
  funext r
  simp only [Pi.smul_apply,smul_eq_mul,canonicalPencil]
  field_simp [hs]
  ring

end
end Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
