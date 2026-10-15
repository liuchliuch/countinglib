import Paper2.ExactInput.PublicRootBound
import Paper2.ExactInput.Reductions

/-! The public answer-size existence theorem discharges the target-convention
premise in hardness transport for every original finite language. -/
namespace Paper2.Problem
open Paper2.ExactInput

/-- Hardness transfers through actual length-controlled oracle machines, with no
extra public-output-size assumption on the ambient language. -/
theorem SharpPHard.transport_unconditional {w : Wiring} {source target : Language}
    (hard : SharpPHard w source) (reduction : Reduces w source target) : SharpPHard w target :=
  hard.transport reduction (boundedAnswers_nonempty w target)

end Paper2.Problem
