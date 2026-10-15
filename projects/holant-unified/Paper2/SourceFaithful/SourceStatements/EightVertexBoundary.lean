import Paper2.SourceFaithful.SourceStatements.EightVertexBoundaryStructural
import Paper2.PublicDichotomyComplete
import Paper2.ExactInput.Coverage

/-! Source Theorem 2.15 with its literal broad quaternary hypothesis and
three common A/P/L exceptions. The structural equivalence genuinely excludes
the extra clauses of the full criterion. Complexity uses the proved strict
original native-X graph and minimal-root output conventions. -/
namespace Paper2.SourceFaithful.SourceStatements.EightVertexBoundary
open Paper2.Tractable Paper2.ExactInput
noncomputable section

/-- Every exact language representing the singleton table has precisely the
source common-transform criterion, irrespective of duplicate table descriptors. -/
theorem criterion (L : Language) (q : Signature AlgebraicComplex 4)
    (hL : L.family = {⟨4,q⟩})
    (heven : HeightTwo.EvenSupport q) (h0 : q (fun _ => false) ≠ 0)
    (h1 : q (fun _ => true) ≠ 0) : Tract (kImage L) ↔ Exception q := by
  change Tract (familyAction sourceKBasis L.family) ↔ Exception q
  rw [hL]
  exact tract_iff_exception q heven h0 h1

/-- Source 2.15: every nonexception is genuinely #P-hard; every common A/P/L
exception has a strict polynomial evaluator. No tensor-prime premise occurs. -/
theorem theorem_2_15 (L : Language) (q : Signature AlgebraicComplex 4)
    (hL : L.family = {⟨4,q⟩})
    (heven : HeightTwo.EvenSupport q) (h0 : q (fun _ => false) ≠ 0)
    (h1 : q (fun _ => true) ≠ 0) :
    (¬Exception q → Problem.SharpPHard .nativeX L) ∧
      (Exception q → Problem.InFP .nativeX L) := by
  have hc := criterion L q hL heven h0 h1
  constructor
  · intro hn
    exact PublicDichotomy.native_hardness L (fun ht => hn (hc.mp ht))
  · intro he
    rcases PublicDichotomy.native_dichotomy L with hf | hh
    · exact hf.2
    · exact (hh.1 (hc.mpr he)).elim

/-- The exact literal problem of every algebraic eight-vertex table exists;
the source statement is not restricted to a promised representable subclass. -/
theorem theorem_2_15_coverage (q : Signature AlgebraicComplex 4)
    (heven : HeightTwo.EvenSupport q) (h0 : q (fun _ => false) ≠ 0)
    (h1 : q (fun _ => true) ≠ 0) :
    ∃ L : Language, L.family = {⟨4,q⟩} ∧
      (¬Exception q → Problem.SharpPHard .nativeX L) ∧
      (Exception q → Problem.InFP .nativeX L) := by
  obtain ⟨L,hL⟩ := Language.coverage_family {⟨4,q⟩} (Set.finite_singleton _)
  exact ⟨L,hL,theorem_2_15 L q hL heven h0 h1⟩

end
end Paper2.SourceFaithful.SourceStatements.EightVertexBoundary

