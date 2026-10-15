import Paper2.Certificates.Q6CoverageCompact.Layer02Part000

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked2_0_3 : checkRange (checkTransitionAt layer1 layer2 next2 (loopOptions 1)) 0 3 = true := by
  decide +kernel

end Paper2.Certificates.Q6.Coverage
