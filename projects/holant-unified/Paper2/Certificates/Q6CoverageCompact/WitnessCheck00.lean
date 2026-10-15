import Paper2.Certificates.Q6CoverageCompact.WitnessData

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_0_8 : checkRange checkTerminalAt 0 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_8_8 : checkRange checkTerminalAt 8 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_0_16 : checkRange checkTerminalAt 0 16 = true := checkRange_join checkTerminalAt 0 8 8 checkedTerminal_0_8 checkedTerminal_8_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_16_8 : checkRange checkTerminalAt 16 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_24_8 : checkRange checkTerminalAt 24 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_16_16 : checkRange checkTerminalAt 16 16 = true := checkRange_join checkTerminalAt 16 8 8 checkedTerminal_16_8 checkedTerminal_24_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_0_32 : checkRange checkTerminalAt 0 32 = true := checkRange_join checkTerminalAt 0 16 16 checkedTerminal_0_16 checkedTerminal_16_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_32_8 : checkRange checkTerminalAt 32 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_40_8 : checkRange checkTerminalAt 40 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_32_16 : checkRange checkTerminalAt 32 16 = true := checkRange_join checkTerminalAt 32 8 8 checkedTerminal_32_8 checkedTerminal_40_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_48_8 : checkRange checkTerminalAt 48 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_56_8 : checkRange checkTerminalAt 56 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_48_16 : checkRange checkTerminalAt 48 16 = true := checkRange_join checkTerminalAt 48 8 8 checkedTerminal_48_8 checkedTerminal_56_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_32_32 : checkRange checkTerminalAt 32 32 = true := checkRange_join checkTerminalAt 32 16 16 checkedTerminal_32_16 checkedTerminal_48_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_0_64 : checkRange checkTerminalAt 0 64 = true := checkRange_join checkTerminalAt 0 32 32 checkedTerminal_0_32 checkedTerminal_32_32

end Paper2.Certificates.Q6.Coverage
