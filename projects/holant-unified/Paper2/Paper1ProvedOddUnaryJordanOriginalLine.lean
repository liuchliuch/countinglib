import Paper2.Paper1ProvedOddUnaryNRJordanPowers
import Paper2.Paper1ProvedOddUnaryWEscapeBinary

/-! The repeated Jordan line has a normalized representative in the
unchanged coefficient field. Its fixed matching orientation is determined
from the checked isotropic line, with the exact nonzero scalar retained. -/
namespace Paper2.Paper1Proved.OddUnary.NRCanonical.JordanReceipt
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.RemoteWork.TractChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {r : ℕ} {a : ℕ→ℕ}
variable {H : (i : Fin r)→Holant.Signature K (a i.val)}
variable {phi : K→+* AlgebraicComplex}

theorem map_repeated (J : NRCanonical.JordanReceipt (H:=H) phi) (v : Bool) :
    phi (NRJordanPowers.repeated J.ratioK v)=J.repeated v/J.repeated false := by
  cases v
  · simp only [NRJordanPowers.repeated,Bool.false_eq_true,ite_false,map_one,
      div_self J.repeatedFalseNonzero]
  · exact J.map_ratioK

/-- No chart coefficient is adjoined: `[1,ratioK]` is computed from the
actual binary graph in the original field. -/
theorem original_line_orientation (J : NRCanonical.JordanReceipt (H:=H) phi) :
    ∃ opposite : Bool,∃ c : AlgebraicComplex,c≠0 ∧
      ∀v,phi (NRJordanPowers.repeated J.ratioK v)=
        c*(TensorDecisionMatching.basis opposite).matrix v false := by
  let A : Holant.Kernel AlgebraicComplex := fun v _=>J.repeated v
  obtain ⟨opposite,c,cnz,form⟩:=WEscape.isotropic_orientation A
    J.repeatedFalseNonzero J.isotropic
  refine ⟨opposite,c/J.repeated false,div_ne_zero cnz J.repeatedFalseNonzero,?_⟩
  intro v
  rw [J.map_repeated]
  have formv : J.repeated v=c*(TensorDecisionMatching.basis opposite).matrix v false:=form v
  rw [formv]
  ring

end
end Paper2.Paper1Proved.OddUnary.NRCanonical.JordanReceipt

