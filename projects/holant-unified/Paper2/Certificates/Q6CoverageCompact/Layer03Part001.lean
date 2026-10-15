import Paper2.Certificates.Q6CoverageCompact.Layer03Part000

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked3_0_4 : checkRange (checkTransitionAt layer2 layer3 next3 (loopOptions 2)) 0 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked3_4_5 : checkRange (checkTransitionAt layer2 layer3 next3 (loopOptions 2)) 4 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked3_0_9 : checkRange (checkTransitionAt layer2 layer3 next3 (loopOptions 2)) 0 9 = true := checkRange_join (checkTransitionAt layer2 layer3 next3 (loopOptions 2)) 0 4 5 checked3_0_4 checked3_4_5

end Paper2.Certificates.Q6.Coverage
