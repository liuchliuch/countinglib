import ComplexCSP.Algebra.AlgebraicInputCompleteness
import ComplexCSP.Instances.Basic
import Mathlib.Logic.Encodable.Pi

/-! # Literal finite encodings of weighted languages

Finite function tables have computable encodings, not unrestricted oracle access.
The signature arities and every individual entry description are part of one
finite natural-number code. Positive arities are a checked subtype condition.
-/
namespace ComplexCSP
open AlgebraicEncoding ComplexRootCertificates

private def algebraicInputDataEquiv : AlgebraicInput ≃ List ℤ × Rectangle where
  toFun a := (a.coefficients,a.rectangle)
  invFun a := ⟨a.1,a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Encodable AlgebraicInput := Encodable.ofEquiv _ algebraicInputDataEquiv

variable {D K ι : Type} [Fintype D] [Encodable D] [Encodable K]
variable [Fintype ι] [Encodable ι]

/-- Every arity and every table entry occurs in this explicit finite code type. -/
abbrev LanguageData := Σ arity : {a : ι → ℕ // ∀ i, 0 < a i},
  (i : ι) → (Fin (arity.val i) → D) → K

def languageDataEquiv : Language D K ι ≃ LanguageData (D := D) (K := K) (ι := ι) where
  toFun L := ⟨⟨L.arity,L.arity_pos⟩,L.value⟩
  invFun a := ⟨a.1.val,a.1.property,a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Computable dependent table encoding through the canonical finite numbering. -/
def languageDataEncodable : Encodable (LanguageData (D := D) (K := K) (ι := ι)) := by
  letI (a : {a : ι → ℕ // ∀ i, 0 < a i}) :
      Encodable ((i : ι) → (Fin (a.val i) → D) → K) :=
    Encodable.ofEquiv
      ((i : Fin (Fintype.card ι)) → (Fin (a.val (Encodable.fintypeEquivFin.symm i)) → D) → K)
      (Equiv.piCongrLeft' _ Encodable.fintypeEquivFin)
  infer_instance

/-- The language structure itself is a finite first-order input encoding. -/
instance : Encodable (Language D K ι) :=
  @Encodable.ofEquiv _ (LanguageData (D := D) (K := K) (ι := ι))
    languageDataEncodable languageDataEquiv

/-- A concrete byte-independent serialization interface, with exact round trip. -/
def encodeLanguage (L : Language D K ι) : ℕ := Encodable.encode L

def decodeLanguage (code : ℕ) : Option (Language D K ι) := Encodable.decode code

@[simp] theorem decode_encodeLanguage (L : Language D K ι) :
    decodeLanguage (encodeLanguage L) = some L := Encodable.encodek L

end ComplexCSP
