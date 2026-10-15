import Paper2.DegreeCSP.GeneratedCoordinateMarginal
import Mathlib.Data.Set.Finite.Basic

/-! A concrete finite enumeration of original language signatures and their
ordered pairs of supported Boolean rows. -/
namespace Paper2.DegreeCSP.OriginalContextCommonPhaseIndex
open Tractable
noncomputable section

/-- A literal language member together with two actual supported rows. -/
def RowPair (F : SignatureFamily AlgebraicComplex) :=
  Σ sf : {sf : AnySignature AlgebraicComplex // sf ∈ F},
    GeneratedCoordinateMarginal.Live sf.val.2 × GeneratedCoordinateMarginal.Live sf.val.2

/-- The finite type is derived from language finiteness and finite Boolean
assignment types, with no namespace-wide instance changes. -/
@[instance_reducible] def rowPairFintype (F : SignatureFamily AlgebraicComplex) (hF : F.Finite) :
    Fintype (RowPair F) := by
  classical
  letI : Fintype {sf : AnySignature AlgebraicComplex // sf ∈ F} := hF.fintype
  unfold RowPair
  infer_instance

/-- The exact number of original supported row pairs. -/
def count (F : SignatureFamily AlgebraicComplex) (hF : F.Finite) : ℕ :=
  @Fintype.card (RowPair F) (rowPairFintype F hF)

/-- The actual finite row-pair enumeration used by the common-phase family. -/
def enumeration (F : SignatureFamily AlgebraicComplex) (hF : F.Finite) :
    RowPair F ≃ Fin (count F hF) :=
  @Fintype.equivFin (RowPair F) (rowPairFintype F hF)

/-- Package two supported rows of the given original language signature. -/
def rowPair {n : ℕ} {f : Signature AlgebraicComplex n}
    (F : SignatureFamily AlgebraicComplex) (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (x y : Fin n → Bool) (hx : f x ≠ 0) (hy : f y ≠ 0) : RowPair F :=
  ⟨⟨⟨n, f⟩, hf⟩, ⟨x, hx⟩, ⟨y, hy⟩⟩

@[simp] theorem rowPair_signature {n : ℕ} {f : Signature AlgebraicComplex n}
    (F : SignatureFamily AlgebraicComplex) (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (x y : Fin n → Bool) (hx : f x ≠ 0) (hy : f y ≠ 0) :
    (rowPair F hf x y hx hy).1.val = (⟨n, f⟩ : AnySignature AlgebraicComplex) := rfl

@[simp] theorem rowPair_left {n : ℕ} {f : Signature AlgebraicComplex n}
    (F : SignatureFamily AlgebraicComplex) (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (x y : Fin n → Bool) (hx : f x ≠ 0) (hy : f y ≠ 0) :
    (rowPair F hf x y hx hy).2.1.val = x := rfl

@[simp] theorem rowPair_right {n : ℕ} {f : Signature AlgebraicComplex n}
    (F : SignatureFamily AlgebraicComplex) (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (x y : Fin n → Bool) (hx : f x ≠ 0) (hy : f y ≠ 0) :
    (rowPair F hf x y hx hy).2.2.val = y := rfl

@[simp] theorem enumeration_decode (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (p : RowPair F) : (enumeration F hF).symm (enumeration F hF p) = p :=
  (enumeration F hF).symm_apply_apply p

end
end Paper2.DegreeCSP.OriginalContextCommonPhaseIndex
