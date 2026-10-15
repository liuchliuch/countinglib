import Paper2.DegreeCSP.AffineThreeFaceDecoder
import Mathlib.Data.Set.Finite.Basic

/-! A finite enumeration of all literal original signatures and all affine
three-bit maps whose eight original coefficients are nonzero. No arity or
rank restriction is imposed: constant and nullary faces are included, and
zero signatures contribute no face. -/
namespace Paper2.DegreeCSP.OriginalLiveThreeFaceIndex
open Tractable
open Holant.Tractable.AffinePhase (Word origin xor)
open Holant.Tractable.TwoTranslate (IsAffineMap)
noncomputable section
set_option backward.isDefEq.respectTransparency false

def Face (F : SignatureFamily AlgebraicComplex) :=
  Σ sf : {sf : AnySignature AlgebraicComplex // sf∈F},
    {p : Word 3→Word sf.val.1 // IsAffineMap p ∧ ∀z,sf.val.2 (p z)≠0}

@[instance_reducible] def faceFintype (F : SignatureFamily AlgebraicComplex) (hF : F.Finite) :
    Fintype (Face F) := by
  classical
  letI : Fintype {sf : AnySignature AlgebraicComplex // sf∈F}:=hF.fintype
  unfold Face
  infer_instance

def count (F : SignatureFamily AlgebraicComplex) (hF : F.Finite) : ℕ :=
  @Fintype.card (Face F) (faceFintype F hF)

def enumeration (F : SignatureFamily AlgebraicComplex) (hF : F.Finite) :
    Face F≃Fin (count F hF) :=
  @Fintype.equivFin (Face F) (faceFintype F hF)

def face {n : ℕ} {f : Signature AlgebraicComplex n}
    (F : SignatureFamily AlgebraicComplex)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (p : Word 3→Word n) (hp : IsAffineMap p) (hlive : ∀z,f (p z)≠0) : Face F :=
  ⟨⟨⟨n,f⟩,hf⟩,⟨p,hp,hlive⟩⟩

@[simp] theorem face_signature {n : ℕ} {f : Signature AlgebraicComplex n}
    (F : SignatureFamily AlgebraicComplex) hf p hp hlive :
    (face (f:=f) F hf p hp hlive).1.val=(⟨n,f⟩ : AnySignature AlgebraicComplex) := rfl

@[simp] theorem face_map {n : ℕ} {f : Signature AlgebraicComplex n}
    (F : SignatureFamily AlgebraicComplex) hf p hp hlive :
    (face (f:=f) F hf p hp hlive).2.val=p := rfl

def lookup (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (i : Fin (count F hF)) : Face F := (enumeration F hF).symm i

def signature (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (i : Fin (count F hF)) : AnySignature AlgebraicComplex := (lookup F hF i).1.val

def map (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (i : Fin (count F hF)) : Word 3→Word (signature F hF i).1 := (lookup F hF i).2.val

theorem member (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (i : Fin (count F hF)) : signature F hF i∈F := (lookup F hF i).1.property

theorem affine (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (i : Fin (count F hF)) : IsAffineMap (map F hF i) := (lookup F hF i).2.property.1

theorem live (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (i : Fin (count F hF)) (z : Word 3) :
    (signature F hF i).2 (map F hF i z)≠0 := (lookup F hF i).2.property.2 z

@[simp] theorem enumeration_decode (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (P : Face F) : lookup F hF (enumeration F hF P)=P :=
  (enumeration F hF).symm_apply_apply P

/-- Every actual original live affine face has a literal slot in this
enumeration. Equality of the dependent packet retains its map and signature. -/
theorem complete {n : ℕ} {f : Signature AlgebraicComplex n}
    (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (p : Word 3→Word n) (hp : IsAffineMap p) (hlive : ∀z,f (p z)≠0) :
    ∃i : Fin (count F hF),lookup F hF i=face F hf p hp hlive :=
  ⟨enumeration F hF (face F hf p hp hlive),enumeration_decode F hF _⟩

theorem no_zero_face {F : SignatureFamily AlgebraicComplex} (P : Face F) :
    P.1.val.2≠0 := by
  intro hz
  exact P.2.property.2 (origin 3) (by simp only [hz,Pi.zero_apply])

theorem count_zero_of_all_zero (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (hz : ∀sf∈F,sf.2=0) : count F hF=0 := by
  let _ : Fintype (Face F):=faceFintype F hF
  let _ : IsEmpty (Face F):=⟨fun P=>no_zero_face P (hz P.1.val P.1.property)⟩
  exact Fintype.card_eq_zero

end
end Paper2.DegreeCSP.OriginalLiveThreeFaceIndex
