import Paper2.DegreeCSP.AllBOAffineResources
import Paper2.DegreeCSP.OriginalCubicGauge
import Paper2.DegreeCSP.OriginalCubicTract

/-! Actual degree-generated block orthogonality gives the unchanged original
tractability criterion for every degree at least two. The proof constructs
all context and mask resources internally, chooses one common phase from
the literal source coefficients, and restores their original affine support.
It imposes no parity restriction and uses no degree-CSP classification record.
-/
namespace Paper2.DegreeCSP.OriginalBOComplete
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem tract_family (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    {k : ℕ} (hk : 2≤k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k) :
    Tract (familyAction sourceKBasis F) := by
  classical
  by_contra hnot
  obtain ⟨ha,c,hc,hmask⟩ := AllBOAffineResources.resources F hF hk hX h0 h1 hBO hnot
  obtain ⟨psi,hpsi,_,hcubes⟩ := OriginalCubicGauge.exists_gauge F hF hk h0 h1 hX
    ha c hc hmask
  apply hnot
  apply OriginalCubicTract.tract_family F hF psi hpsi
  · exact BooleanGeneratedAffineSupport.original_support_xor F (by omega) hX hBO
  · intro f hf p hp hlive
    exact hcubes f.2 hf p hp hlive

end
end Paper2.DegreeCSP.OriginalBOComplete
