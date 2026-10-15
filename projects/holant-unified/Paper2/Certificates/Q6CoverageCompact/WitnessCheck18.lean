import Paper2.Certificates.Q6CoverageCompact.WitnessCheck17

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1152_8 : checkRange checkTerminalAt 1152 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1160_8 : checkRange checkTerminalAt 1160 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1152_16 : checkRange checkTerminalAt 1152 16 = true := checkRange_join checkTerminalAt 1152 8 8 checkedTerminal_1152_8 checkedTerminal_1160_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1168_8 : checkRange checkTerminalAt 1168 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1176_8 : checkRange checkTerminalAt 1176 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1168_16 : checkRange checkTerminalAt 1168 16 = true := checkRange_join checkTerminalAt 1168 8 8 checkedTerminal_1168_8 checkedTerminal_1176_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1152_32 : checkRange checkTerminalAt 1152 32 = true := checkRange_join checkTerminalAt 1152 16 16 checkedTerminal_1152_16 checkedTerminal_1168_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1184_8 : checkRange checkTerminalAt 1184 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1192_8 : checkRange checkTerminalAt 1192 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1184_16 : checkRange checkTerminalAt 1184 16 = true := checkRange_join checkTerminalAt 1184 8 8 checkedTerminal_1184_8 checkedTerminal_1192_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1200_8 : checkRange checkTerminalAt 1200 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1208_8 : checkRange checkTerminalAt 1208 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1200_16 : checkRange checkTerminalAt 1200 16 = true := checkRange_join checkTerminalAt 1200 8 8 checkedTerminal_1200_8 checkedTerminal_1208_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1184_32 : checkRange checkTerminalAt 1184 32 = true := checkRange_join checkTerminalAt 1184 16 16 checkedTerminal_1184_16 checkedTerminal_1200_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1152_64 : checkRange checkTerminalAt 1152 64 = true := checkRange_join checkTerminalAt 1152 32 32 checkedTerminal_1152_32 checkedTerminal_1184_32

end Paper2.Certificates.Q6.Coverage
