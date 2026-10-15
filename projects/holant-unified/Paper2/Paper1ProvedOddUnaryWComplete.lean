import Paper2.Paper1ProvedOddUnaryJordanWholeSource
import Paper2.Paper1ProvedOddUnaryJordanBothPinHardness
import Paper2.Paper1ProvedOddUnaryProvider

/-! The ordinary-isotropic W source is closed without a unary classifier
premise. Every matching escape, product cap, Jordan interpolation and final
trace-zero graph is constructed in the original field, and its executed
controlled programme returns to the unchanged ordinary input language. -/
namespace Paper2.Paper1Proved.OddUnary
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IsotropicWSource
variable {L : Paper2.ExactInput.Language} (S : IsotropicWSource L)

include S in
theorem hard : Paper2.FixedFieldOutput.SharpPHard .ordinary L := by
  obtain ⟨D⟩:=S.tracezero_pin_packet
  exact JordanTraceZeroPins.Packet.hard S.source D

end IsotropicWSource

namespace UnaryProvider

/-- The actual W consumer has no structural resource or classification
parameter. Its only input is the source packet produced by unary descent. -/
theorem provedWConsumer : WConsumer:=fun _ S=>S.hard

end UnaryProvider
end
end Paper2.Paper1Proved.OddUnary

