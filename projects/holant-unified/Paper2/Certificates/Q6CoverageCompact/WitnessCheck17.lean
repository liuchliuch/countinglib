import Paper2.Certificates.Q6CoverageCompact.WitnessCheck16

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1088_8 : checkRange checkTerminalAt 1088 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1096_8 : checkRange checkTerminalAt 1096 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1088_16 : checkRange checkTerminalAt 1088 16 = true := checkRange_join checkTerminalAt 1088 8 8 checkedTerminal_1088_8 checkedTerminal_1096_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1104_8 : checkRange checkTerminalAt 1104 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1112_8 : checkRange checkTerminalAt 1112 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1104_16 : checkRange checkTerminalAt 1104 16 = true := checkRange_join checkTerminalAt 1104 8 8 checkedTerminal_1104_8 checkedTerminal_1112_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1088_32 : checkRange checkTerminalAt 1088 32 = true := checkRange_join checkTerminalAt 1088 16 16 checkedTerminal_1088_16 checkedTerminal_1104_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1120_8 : checkRange checkTerminalAt 1120 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1128_8 : checkRange checkTerminalAt 1128 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1120_16 : checkRange checkTerminalAt 1120 16 = true := checkRange_join checkTerminalAt 1120 8 8 checkedTerminal_1120_8 checkedTerminal_1128_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1136_8 : checkRange checkTerminalAt 1136 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1144_8 : checkRange checkTerminalAt 1144 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1136_16 : checkRange checkTerminalAt 1136 16 = true := checkRange_join checkTerminalAt 1136 8 8 checkedTerminal_1136_8 checkedTerminal_1144_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1120_32 : checkRange checkTerminalAt 1120 32 = true := checkRange_join checkTerminalAt 1120 16 16 checkedTerminal_1120_16 checkedTerminal_1136_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1088_64 : checkRange checkTerminalAt 1088 64 = true := checkRange_join checkTerminalAt 1088 32 32 checkedTerminal_1088_32 checkedTerminal_1120_32

end Paper2.Certificates.Q6.Coverage
