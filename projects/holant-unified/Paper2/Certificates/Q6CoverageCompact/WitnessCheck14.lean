import Paper2.Certificates.Q6CoverageCompact.WitnessCheck13

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_896_8 : checkRange checkTerminalAt 896 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_904_8 : checkRange checkTerminalAt 904 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_896_16 : checkRange checkTerminalAt 896 16 = true := checkRange_join checkTerminalAt 896 8 8 checkedTerminal_896_8 checkedTerminal_904_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_912_8 : checkRange checkTerminalAt 912 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_920_8 : checkRange checkTerminalAt 920 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_912_16 : checkRange checkTerminalAt 912 16 = true := checkRange_join checkTerminalAt 912 8 8 checkedTerminal_912_8 checkedTerminal_920_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_896_32 : checkRange checkTerminalAt 896 32 = true := checkRange_join checkTerminalAt 896 16 16 checkedTerminal_896_16 checkedTerminal_912_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_928_8 : checkRange checkTerminalAt 928 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_936_8 : checkRange checkTerminalAt 936 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_928_16 : checkRange checkTerminalAt 928 16 = true := checkRange_join checkTerminalAt 928 8 8 checkedTerminal_928_8 checkedTerminal_936_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_944_8 : checkRange checkTerminalAt 944 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_952_8 : checkRange checkTerminalAt 952 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_944_16 : checkRange checkTerminalAt 944 16 = true := checkRange_join checkTerminalAt 944 8 8 checkedTerminal_944_8 checkedTerminal_952_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_928_32 : checkRange checkTerminalAt 928 32 = true := checkRange_join checkTerminalAt 928 16 16 checkedTerminal_928_16 checkedTerminal_944_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_896_64 : checkRange checkTerminalAt 896 64 = true := checkRange_join checkTerminalAt 896 32 32 checkedTerminal_896_32 checkedTerminal_928_32

end Paper2.Certificates.Q6.Coverage
