import Paper2.DegreeCSP.AffineThreeFaceDecoder
import Paper2.DegreeCSP.MultiCoordinateContextDegrees

/-! Physical partial presentations of an original affine three-face map and
all eight of its coordinate-zero faces. Each uses the original constraint
once; literal pin/X caps complete hidden degrees to k and preserve every
original coefficient on the seven-character code. -/
namespace Paper2.DegreeCSP.OriginalThreeFaceContext
open Tractable TensorDecomposition
open Holant.Tractable.AffinePhase (Word origin xor)
open Holant.Tractable.TwoTranslate (IsAffineMap)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def zeroFace (u z : Word 3) : Word 3 := fun i => z i && u i
def faceMap (p : Word 3 → Word n) (u : Word 3) : Word 3 → Word n :=
  fun z => p (zeroFace u z)

theorem zeroFace_origin (u : Word 3) : zeroFace u (origin 3) = origin 3 := rfl

theorem zeroFace_xor (u x y : Word 3) :
    zeroFace u (xor x y) = xor (zeroFace u x) (zeroFace u y) := by
  funext i
  change ((Bool.xor (x i) (y i)) && u i) = Bool.xor (x i && u i) (y i && u i)
  cases x i <;> cases y i <;> cases u i <;> rfl

theorem faceMap_affine (p : Word 3 → Word n) (hp : IsAffineMap p) (u : Word 3) :
    IsAffineMap (faceMap p u) := by
  intro x y
  simp only [faceMap,zeroFace_xor,zeroFace_origin]
  exact hp (zeroFace u x) (zeroFace u y)

abbrev presentation (p : Word 3 → Word n) (f : Signature AlgebraicComplex n)
    (k : ℕ) : Presentation AlgebraicComplex (Fin 7) :=
  MultiCoordinateContext.context (AffineThreeFaceDecoder.decoder p) f (k-1)

abbrev facePresentation (p : Word 3 → Word n) (f : Signature AlgebraicComplex n)
    (k : ℕ) (u : Word 3) : Presentation AlgebraicComplex (Fin 7) :=
  presentation (faceMap p u) f k

theorem uses (p : Word 3 → Word n) (f : Signature AlgebraicComplex n) (k : ℕ)
    (F : SignatureFamily AlgebraicComplex)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F) :
    (presentation p f k).Uses F :=
  MultiCoordinateContext.uses (AffineThreeFaceDecoder.decoder p) F f hf h0 h1 hX (k-1)

theorem hidden_degree (p : Word 3 → Word n) (f : Signature AlgebraicComplex n)
    {k : ℕ} (hk : 0 < k) (h : MultiCoordinateContext.Hidden (AffineThreeFaceDecoder.decoder p)) :
    (presentation p f k).degree (OrderedPresentation.variableEquiv (Sum.inr h)) = k := by
  rw [MultiCoordinateContext.hidden_degree]
  omega

theorem hidden_divisible (p : Word 3 → Word n) (f : Signature AlgebraicComplex n)
    {k : ℕ} (hk : 0 < k) : PartialUnaryProducts.HiddenDivisible (presentation p f k) k := by
  apply MultiCoordinateContext.hidden_divisible
  have he : k-1+1=k := by omega
  rw [he]

theorem boundary_degree (p : Word 3 → Word n) (f : Signature AlgebraicComplex n)
    (k : ℕ) (j : Fin 7) :
    (presentation p f k).degree (Sum.inl j) =
      MultiCoordinateContext.boundaryWeight (AffineThreeFaceDecoder.decoder p) (k-1) j :=
  MultiCoordinateContext.boundary_degree (AffineThreeFaceDecoder.decoder p) f (k-1) j

/-- The literal value keeps one original coefficient on every codeword. -/
theorem value_code (p : Word 3 → Word n) (hp : IsAffineMap p)
    (f : Signature AlgebraicComplex n) {k : ℕ} (hk : 2 ≤ k) (z : Word 3) :
    (presentation p f k).value (GeneratedCodeSeven.code z) = f (p z) := by
  change (MultiCoordinateContext.context (AffineThreeFaceDecoder.decoder p) f (k-1)).value _ = _
  rw [MultiCoordinateContext.value _ f (by omega),AffineThreeFaceDecoder.decoder_correct p hp]

theorem face_uses (p : Word 3 → Word n) (f : Signature AlgebraicComplex n) (k : ℕ)
    (F : SignatureFamily AlgebraicComplex)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (u : Word 3) : (facePresentation p f k u).Uses F :=
  uses (faceMap p u) f k F hf h0 h1 hX

theorem face_hidden_divisible (p : Word 3 → Word n) (f : Signature AlgebraicComplex n)
    {k : ℕ} (hk : 0 < k) (u : Word 3) :
    PartialUnaryProducts.HiddenDivisible (facePresentation p f k u) k :=
  hidden_divisible (faceMap p u) f hk

theorem face_boundary_degree (p : Word 3 → Word n) (f : Signature AlgebraicComplex n)
    (k : ℕ) (u : Word 3) (j : Fin 7) :
    (facePresentation p f k u).degree (Sum.inl j) =
      MultiCoordinateContext.boundaryWeight (AffineThreeFaceDecoder.decoder (faceMap p u)) (k-1) j :=
  boundary_degree (faceMap p u) f k j

theorem face_value_code (p : Word 3 → Word n) (hp : IsAffineMap p)
    (f : Signature AlgebraicComplex n) {k : ℕ} (hk : 2 ≤ k) (u z : Word 3) :
    (facePresentation p f k u).value (GeneratedCodeSeven.code z) = f (p (zeroFace u z)) :=
  value_code (faceMap p u) (faceMap_affine p hp u) f hk z

end
end Paper2.DegreeCSP.OriginalThreeFaceContext
