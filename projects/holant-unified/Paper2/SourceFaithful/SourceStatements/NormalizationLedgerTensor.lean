import Paper2.SourceFaithful.SourceStatements.NormalizationLedgerSteps

/-! The exact dictionary between the ledger's inverse tensor action and the
source expression `h ∝ A^(⊗arity) h₀` with every entry of `h₀` in the one field. -/
namespace Paper2.SourceFaithful.SourceStatements.NormalizationLedger
noncomputable section
open Tractable ExactInput Paper2.HeightOne.PhaseCards

lemma action_scale (A : InvertibleKernel) {n : ℕ} (c : AlgebraicComplex)
    (f : Signature AlgebraicComplex n) :
    A.action (fun x => c * f x) = fun x => c * A.action f x := by
  classical
  funext x
  simp only [InvertibleKernel.action, Signature.coordinateAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

def ProjectiveImageOver (E : Subfield AlgebraicComplex) (A : InvertibleKernel)
    (f : AnySignature AlgebraicComplex) : Prop :=
  ∃ h₀ : Signature AlgebraicComplex f.1, (∀ x, h₀ x ∈ E) ∧
    ∃ c : AlgebraicComplex, c ≠ 0 ∧ f.2 = fun x => c * A.action h₀ x

theorem pullbackOver_iff_projectiveImageOver (E : Subfield AlgebraicComplex)
    (A : InvertibleKernel) (f : AnySignature AlgebraicComplex) :
    PullbackOver E A f ↔ ProjectiveImageOver E A f := by
  constructor
  · rintro ⟨c, hc, hcoeff⟩
    refine ⟨fun x => c * A.symm.action f.2 x, hcoeff, c⁻¹, inv_ne_zero hc, ?_⟩
    rw [action_scale, InvertibleKernel.action_symm_action]
    funext x
    simp [hc]
  · rintro ⟨h₀, hcoeff, c, hc, hf⟩
    change ProjectivelyOver E (A.symm.action f.2)
    rw [hf, action_scale, InvertibleKernel.symm_action_action]
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    intro x
    simpa [hc] using hcoeff x

/-- The source fixes a field containing the literal original entries. The
proof remains valid for any such subfield, in particular its prescribed
number field including conjugates and constants fixed before construction. -/
def OriginalCoefficients (E : Subfield AlgebraicComplex) (G : Language) : Prop :=
  ∀ f ∈ G.family, ∀ x, f.2 x ∈ E

lemma OriginalCoefficients.projective {E : Subfield AlgebraicComplex} {G : Language}
    (h : OriginalCoefficients E G) : ∀ f ∈ G.family, ProjectivelyOver E f.2 := by
  intro f hf
  exact ⟨1, one_ne_zero, fun x => by simpa using h f hf x⟩

lemma Ledger.projectiveImage {E : Subfield AlgebraicComplex} {G : Language} {S : State}
    (h : Ledger E G S) : ∀ f ∈ S.language.family, ProjectiveImageOver E S.coordinates f :=
  fun f hf => (pullbackOver_iff_projectiveImageOver E S.coordinates f).mp (h.field f hf)

end
end Paper2.SourceFaithful.SourceStatements.NormalizationLedger

