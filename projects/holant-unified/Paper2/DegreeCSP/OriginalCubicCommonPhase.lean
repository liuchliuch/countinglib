import Paper2.DegreeCSP.PartialTernaryCubicPacket
import Paper2.DegreeCSP.OriginalLiveThreeFaceIndex
import Paper2.DegreeCSP.GeneratedCodeSeven

/-! All live affine three-bit maps of the finite original language are
included in one finite family of concrete eight-face contexts. Their true
degree cycles select a single character for the original cubic ratios,
including maps of rank zero, one and two. -/
namespace Paper2.DegreeCSP.OriginalCubicCommonPhase
open Tractable TensorDecomposition
open Holant.Tractable.AffinePhase (Word)
open Holant.Tractable.TwoTranslate (IsAffineMap)
noncomputable section
set_option backward.isDefEq.respectTransparency false

def facePacket (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    {k : ℕ} (hk : 2≤k)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (unary : ∀g : Signature AlgebraicComplex 1,Generated F k g→Affine g)
    (q : OriginalLiveThreeFaceIndex.Face F) : CubicContextCharacter.Packet F k :=
  PartialTernaryCubicContext.originalPacket F hF hk h0 h1 hX unary
    q.2.val q.2.property.1 q.1.val.2 q.1.property q.2.property.2

def packets (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    {k : ℕ} (hk : 2≤k)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (unary : ∀g : Signature AlgebraicComplex 1,Generated F k g→Affine g) :
    Fin (OriginalLiveThreeFaceIndex.count F hF)→CubicContextCharacter.Packet F k :=
  fun i=>facePacket F hF hk h0 h1 hX unary (OriginalLiveThreeFaceIndex.lookup F hF i)

theorem common_phase (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    {k : ℕ} (hk : 2≤k)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (affine : ∀{n}(f : Signature AlgebraicComplex n),Generated F k f→Affine f)
    (maskScalar : AlgebraicComplex) (hm : maskScalar≠0)
    (mask : Generated F k (fun y=>maskScalar*GeneratedCodeSeven.indicator y)) :
    ∃theta : AlgebraicComplex,theta^k=1 ∧
      ∀{n}(f : Signature AlgebraicComplex n),
        (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F→
        ∀p : Word 3→Word n,IsAffineMap p→(∀z,f (p z)≠0)→
          PartialTernaryCubicContext.parameter p f=
            theta^(PartialTernaryCubicContext.charge p f k) := by
  let unary : ∀g : Signature AlgebraicComplex 1,Generated F k g→Affine g :=
    fun g hg=>affine g hg
  obtain ⟨theta,hcycle,hslots⟩ := CubicContextCharacter.exists_phase (by omega)
    (packets F hF hk h0 h1 hX unary) maskScalar hm mask affine
  refine ⟨theta,hcycle,?_⟩
  intro n f hf p hp hlive
  let q := OriginalLiveThreeFaceIndex.face F hf p hp hlive
  let i := OriginalLiveThreeFaceIndex.enumeration F hF q
  have h := hslots i
  have he : OriginalLiveThreeFaceIndex.lookup F hF i=q :=
    OriginalLiveThreeFaceIndex.enumeration_decode F hF q
  change (facePacket F hF hk h0 h1 hX unary
    (OriginalLiveThreeFaceIndex.lookup F hF i)).parameter=theta^
    (facePacket F hF hk h0 h1 hX unary
      (OriginalLiveThreeFaceIndex.lookup F hF i)).charge at h
  rw [he] at h
  exact h

end
end Paper2.DegreeCSP.OriginalCubicCommonPhase
