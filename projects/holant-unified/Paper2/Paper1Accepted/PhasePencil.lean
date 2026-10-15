import Paper2.Tractable.Scalars
import Mathlib.Tactic

/-! Exact, purely algebraic Paper 1 Lemma 7.1 (arXiv:2609.00219v1,
printed pp.119--120, PDF pages 118--119). This accepted statement has no
complexity/output-code interface and no Paper 2 classification conclusion.
The power equation is the literal definition of membership in μ_N. -/
namespace Paper2
open Tractable
namespace PhasePencil

def Root (N : ℕ) (a : AlgebraicComplex) : Prop := a ^ N = 1

def Relation (N : ℕ) (a b c d : AlgebraicComplex) : Prop :=
  ∃ α : AlgebraicComplex, Root N α ∧
    ((c = -α * a ∧ d = -α * b) ∨
     (b = 0 ∧ c = 0 ∧ d = α * a) ∨
     (a = 0 ∧ d = 0 ∧ c = α * b))

/-- Exactly diag(a-sb,c-sd) Z = 0 or a nonzero multiple of D_eta. -/
def Safe (N : ℕ) (a b c d : AlgebraicComplex) : Prop :=
  ∀ s : AlgebraicComplex, Root N s →
    (a - s * b = 0 ∧ c - s * d = 0) ∨
    ∃ η κ : AlgebraicComplex, Root N η ∧ κ ≠ 0 ∧
      a - s * b = κ ∧ c - s * d = -κ * η

end PhasePencil

structure Paper1PhasePencilAccepted where
  /-- Official Lemma 7.1, including zero pencils and all three alternatives. -/
  phasePencil_7_1 : ∀ (N : ℕ), 3 ≤ N → ∀ a b c d : AlgebraicComplex,
    PhasePencil.Relation N a b c d ↔ PhasePencil.Safe N a b c d

end Paper2
