import Paper2.Certificates.Q6CoverageCompact.Layer04Part000

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked4_0_6 : checkRange (checkTransitionAt layer3 layer4 next4 (loopOptions 3)) 0 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked4_6_7 : checkRange (checkTransitionAt layer3 layer4 next4 (loopOptions 3)) 6 7 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked4_0_13 : checkRange (checkTransitionAt layer3 layer4 next4 (loopOptions 3)) 0 13 = true := checkRange_join (checkTransitionAt layer3 layer4 next4 (loopOptions 3)) 0 6 7 checked4_0_6 checked4_6_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked4_13_7 : checkRange (checkTransitionAt layer3 layer4 next4 (loopOptions 3)) 13 7 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked4_20_7 : checkRange (checkTransitionAt layer3 layer4 next4 (loopOptions 3)) 20 7 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked4_13_14 : checkRange (checkTransitionAt layer3 layer4 next4 (loopOptions 3)) 13 14 = true := checkRange_join (checkTransitionAt layer3 layer4 next4 (loopOptions 3)) 13 7 7 checked4_13_7 checked4_20_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked4_0_27 : checkRange (checkTransitionAt layer3 layer4 next4 (loopOptions 3)) 0 27 = true := checkRange_join (checkTransitionAt layer3 layer4 next4 (loopOptions 3)) 0 13 14 checked4_0_13 checked4_13_14

end Paper2.Certificates.Q6.Coverage
