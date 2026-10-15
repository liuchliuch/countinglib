import Paper2.Certificates.Q6CoverageCompact.Layer01Part000

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked1_0_1 : checkRange (checkTransitionAt layer0 layer1 next1 (loopOptions 0)) 0 1 = true := by
  decide +kernel

end Paper2.Certificates.Q6.Coverage
