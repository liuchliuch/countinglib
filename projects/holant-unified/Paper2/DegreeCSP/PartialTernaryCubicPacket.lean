import Paper2.DegreeCSP.PartialTernaryCubicContext
import Paper2.DegreeCSP.CubicContextCharacter
import Paper2.DegreeCSP.OriginalPhaseInverse

/-! The checked eight-face presentation supplies a concrete common-character
packet. For an original language member its high-power identities follow from
actual generated unary affinity; they are not an additional certificate. -/
namespace Paper2.DegreeCSP.PartialTernaryCubicContext
open Tractable TensorDecomposition
open Holant.Tractable.AffinePhase (Word origin)
open Holant.Tractable.TwoTranslate (IsAffineMap)
noncomputable section
set_option backward.isDefEq.respectTransparency false

def packet {F : SignatureFamily AlgebraicComplex} {n k : ℕ}
    (p : Word 3→Word n) (hp : IsAffineMap p)
    (f : Signature AlgebraicComplex n) (hk : 2≤k)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (ha : ∀z,f (p z)≠0)
    (hpower : ∀z,f (p z)^(4*k)=f (p (origin 3))^(4*k)) :
    CubicContextCharacter.Packet F k where
  presentation := presentation p f k
  charge := charge p f k
  scalar := scalar p f k
  parameter := parameter p f
  scalar_nonzero := scalar_nonzero p f k ha
  parameter_nonzero := parameter_nonzero p f ha
  uses := uses p f k F hf h0 h1 hX
  hidden := hidden_divisible p f (by omega)
  boundary j := by
    rw [boundary_charge p f (by omega)]
    have he : SignedCubeNormalizer.bundleSign j=CubicContextCharacter.sign j := by
      fin_cases j <;> norm_num [SignedCubeNormalizer.bundleSign,CubicContextCharacter.sign]
    rw [he]
  on_code x := value_code p hp f hk ha hpower x

def originalPacket (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    {n k : ℕ} (hk : 2≤k)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (unary : ∀g : Signature AlgebraicComplex 1,Generated F k g→Affine g)
    (p : Word 3→Word n) (hp : IsAffineMap p)
    (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (ha : ∀z,f (p z)≠0) : CubicContextCharacter.Packet F k :=
  packet p hp f hk hf h0 h1 hX ha (fun z=>
    OriginalPhaseInverse.uniform_power F hF (by omega) h0 h1 hX unary f hf
      (p (origin 3)) (p z) (ha (origin 3)) (ha z))

end
end Paper2.DegreeCSP.PartialTernaryCubicContext
