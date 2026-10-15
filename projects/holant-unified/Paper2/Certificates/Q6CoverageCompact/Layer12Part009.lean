import Paper2.Certificates.Q6CoverageCompact.Layer12Part008

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_0_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 0 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_6_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 6 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_0_12 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 0 12 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 0 6 6 checked12_0_6 checked12_6_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_12_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 12 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_18_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 18 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_12_12 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 12 12 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 12 6 6 checked12_12_6 checked12_18_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_0_24 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 0 24 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 0 12 12 checked12_0_12 checked12_12_12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_24_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 24 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_30_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 30 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_24_12 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 24 12 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 24 6 6 checked12_24_6 checked12_30_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_36_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 36 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_42_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 42 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_36_12 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 36 12 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 36 6 6 checked12_36_6 checked12_42_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_24_24 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 24 24 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 24 12 12 checked12_24_12 checked12_36_12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_0_48 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 0 48 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 0 24 24 checked12_0_24 checked12_24_24

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_48_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 48 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_54_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 54 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_48_12 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 48 12 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 48 6 6 checked12_48_6 checked12_54_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_60_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 60 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_66_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 66 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_60_12 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 60 12 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 60 6 6 checked12_60_6 checked12_66_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_48_24 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 48 24 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 48 12 12 checked12_48_12 checked12_60_12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_72_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 72 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_78_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 78 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_72_12 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 72 12 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 72 6 6 checked12_72_6 checked12_78_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_84_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 84 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_90_7 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 90 7 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_84_13 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 84 13 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 84 6 7 checked12_84_6 checked12_90_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_72_25 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 72 25 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 72 12 13 checked12_72_12 checked12_84_13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_48_49 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 48 49 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 48 24 25 checked12_48_24 checked12_72_25

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_0_97 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 0 97 = true := checkRange_join (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 0 48 49 checked12_0_48 checked12_48_49

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked12_97_6 : checkRange (checkTransitionAt layer11 layer12 next12 (loopOptions 11)) 97 6 = true := by
  decide +kernel

end Paper2.Certificates.Q6.Coverage
