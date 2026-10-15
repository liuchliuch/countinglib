import ComplexCSP.Recognition.UniformAlgebraicDegreeGlobal
import ComplexCSP.Instances.LanguageEncoding

/-! # One finite input code, including domain and signature sizes

This frontend makes the uniformity in domain size, language size, positive arities,
and all algebraic coefficients explicit. There is no hidden fixed number field.
-/
namespace ComplexCSP.Recognition
open AlgebraicEncoding

/-- All sizes, arities, tables, integer polynomials and rectangles are runtime data. -/
structure FiniteAlgebraicLanguage where
  domainSize : ℕ
  domain_pos : 0 < domainSize
  signatureSize : ℕ
  tables : Language (Fin domainSize) AlgebraicInput (Fin signatureSize)

abbrev FiniteAlgebraicLanguageData := Σ d : {d : ℕ // 0 < d},
  Σ s : ℕ, Language (Fin d.val) AlgebraicInput (Fin s)

def finiteAlgebraicLanguageEquiv : FiniteAlgebraicLanguage ≃ FiniteAlgebraicLanguageData where
  toFun L := ⟨⟨L.domainSize,L.domain_pos⟩,L.signatureSize,L.tables⟩
  invFun x := ⟨x.1.val,x.1.property,x.2.1,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Encodable FiniteAlgebraicLanguage :=
  Encodable.ofEquiv FiniteAlgebraicLanguageData finiteAlgebraicLanguageEquiv

def FiniteAlgebraicLanguage.Valid (L : FiniteAlgebraicLanguage) : Prop :=
  ValidAlgebraicLanguage L.tables

/-- Ordinary uniform recognition from one explicitly finite encoded input. -/
def encodedGlobalTest (L : FiniteAlgebraicLanguage) (hL : L.Valid) : Bool :=
  uniformAlgebraicGlobalTest L.tables hL

/-- Degree-multiple uniform recognition, with the modulus also a runtime input. -/
def encodedDegreeGlobalTest (L : FiniteAlgebraicLanguage) (hL : L.Valid)
    (δ : ℕ) (hδ : 0 < δ) : Bool := uniformAlgebraicDegreeGlobalTest L.tables hL δ hδ

 theorem encodedGlobalTest_correct (L : FiniteAlgebraicLanguage) (hL : L.Valid)
    (z : ∀ i, (Fin (L.tables.arity i) → Fin L.domainSize) → ℂ)
    (hz : ∀ i a, (L.tables.value i a).Represents (z i a)) :
    encodedGlobalTest L hL = true ↔ CaiChenConditions (realizedAlgebraicLanguage L.tables z) := by
  letI : NeZero L.domainSize := ⟨Nat.ne_zero_of_lt L.domain_pos⟩
  exact uniformAlgebraicGlobalTest_correct_conditions L.tables hL z hz

 theorem encodedDegreeGlobalTest_correct (L : FiniteAlgebraicLanguage) (hL : L.Valid)
    (δ : ℕ) (hδ : 0 < δ)
    (z : ∀ i, (Fin (L.tables.arity i) → Fin L.domainSize) → ℂ)
    (hz : ∀ i a, (L.tables.value i a).Represents (z i a)) :
    encodedDegreeGlobalTest L hL δ hδ = true ↔
      DegreeCaiChenConditions (realizedAlgebraicLanguage L.tables z) δ := by
  letI : NeZero L.domainSize := ⟨Nat.ne_zero_of_lt L.domain_pos⟩
  exact uniformAlgebraicDegreeGlobalTest_correct_conditions L.tables hL δ hδ z hz

/-- A literal natural-code round trip includes every input datum. -/
 theorem finiteAlgebraicLanguage_decode_encode (L : FiniteAlgebraicLanguage) :
    Encodable.decode (Encodable.encode L) = some L := Encodable.encodek L

end ComplexCSP.Recognition
