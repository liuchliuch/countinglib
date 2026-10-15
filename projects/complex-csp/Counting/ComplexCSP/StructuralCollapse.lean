import ComplexCSP.Structure.StructuralCollapse

/-! Public structural endpoint for finite nonempty domains and algebraic complex languages. -/
namespace Counting.ComplexCSP

theorem structural_collapse {D ι : Type} [Fintype D] [Nonempty D] [Fintype ι]
    (L : _root_.ComplexCSP.Language D ℂ ι)
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    _root_.ComplexCSP.CaiChenConditions L ↔ _root_.ComplexCSP.JointBO L :=
  _root_.ComplexCSP.structural_collapse L hAlg

theorem jointBO_global_type_partition {D ι : Type} [Fintype D] [Nonempty D] [Fintype ι]
    (L : _root_.ComplexCSP.Language D ℂ ι)
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (hBO : _root_.ComplexCSP.JointBO L) :
    _root_.ComplexCSP.GlobalTypePartition L :=
  _root_.ComplexCSP.JointBO.global_type_partition L hAlg hBO

theorem jointBO_global_maltsev {D ι : Type} [Fintype D] [Nonempty D] [Fintype ι]
    (L : _root_.ComplexCSP.Language D ℂ ι)
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (hBO : _root_.ComplexCSP.JointBO L) :
    _root_.ComplexCSP.GlobalMaltsev L :=
  _root_.ComplexCSP.JointBO.global_maltsev L hAlg hBO

end Counting.ComplexCSP
