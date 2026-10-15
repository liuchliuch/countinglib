import ComplexCSP.Structure.DegreeStructuralCollapse

/-! Degree conditions use actual occurrence multiplicities and the same generated family. -/
namespace Counting.ComplexCSP

theorem degree_structural_collapse {D ι : Type} [Fintype D] [Nonempty D] [Fintype ι]
    (L : _root_.ComplexCSP.Language D ℂ ι) (δ : ℕ)
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    _root_.ComplexCSP.DegreeCaiChenConditions L δ ↔ _root_.ComplexCSP.DegreeJointBO L δ :=
  _root_.ComplexCSP.degree_structural_collapse L δ hAlg

theorem degree_conditions_at_one {D ι : Type} [Fintype D]
    (L : _root_.ComplexCSP.Language D ℂ ι) :
    _root_.ComplexCSP.DegreeCaiChenConditions L 1 ↔ _root_.ComplexCSP.CaiChenConditions L :=
  _root_.ComplexCSP.degreeCaiChenConditions_one_iff L

end Counting.ComplexCSP
