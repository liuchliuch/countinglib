import ComplexCSP.Recognition.UniformAlgebraicEncoded

/-! The original terminating recognizer on exact finite algebraic input. No uniform time bound is asserted. -/
namespace Counting.ComplexCSP.Recognition

abbrev FiniteAlgebraicLanguage := _root_.ComplexCSP.Recognition.FiniteAlgebraicLanguage
abbrev AlgebraicInput := _root_.ComplexCSP.AlgebraicEncoding.AlgebraicInput

/-- Runtime data include the positive domain size, all arities and all exact entries. -/
def recognize (L : FiniteAlgebraicLanguage) (hL : L.Valid) : Bool :=
  _root_.ComplexCSP.Recognition.encodedGlobalTest L hL

/-- The positive occurrence-degree modulus is also runtime input. -/
def recognizeDegree (L : FiniteAlgebraicLanguage) (hL : L.Valid)
    (δ : ℕ) (hδ : 0 < δ) : Bool :=
  _root_.ComplexCSP.Recognition.encodedDegreeGlobalTest L hL δ hδ

theorem recognize_correct (L : FiniteAlgebraicLanguage) (hL : L.Valid)
    (z : ∀ i, (Fin (L.tables.arity i) → Fin L.domainSize) → ℂ)
    (hz : ∀ i a, (L.tables.value i a).Represents (z i a)) :
    recognize L hL = true ↔ _root_.ComplexCSP.CaiChenConditions
      (_root_.ComplexCSP.Recognition.realizedAlgebraicLanguage L.tables z) :=
  _root_.ComplexCSP.Recognition.encodedGlobalTest_correct L hL z hz

theorem recognizeDegree_correct (L : FiniteAlgebraicLanguage) (hL : L.Valid)
    (δ : ℕ) (hδ : 0 < δ)
    (z : ∀ i, (Fin (L.tables.arity i) → Fin L.domainSize) → ℂ)
    (hz : ∀ i a, (L.tables.value i a).Represents (z i a)) :
    recognizeDegree L hL δ hδ = true ↔ _root_.ComplexCSP.DegreeCaiChenConditions
      (_root_.ComplexCSP.Recognition.realizedAlgebraicLanguage L.tables z) δ :=
  _root_.ComplexCSP.Recognition.encodedDegreeGlobalTest_correct L hL δ hδ z hz

theorem decode_encode (L : FiniteAlgebraicLanguage) :
    Encodable.decode (Encodable.encode L) = some L :=
  _root_.ComplexCSP.Recognition.finiteAlgebraicLanguage_decode_encode L

theorem representation_unique {a : AlgebraicInput} {z w : ℂ}
    (hz : a.Represents z) (hw : a.Represents w) : w = z :=
  hz.unique hw

end Counting.ComplexCSP.Recognition
