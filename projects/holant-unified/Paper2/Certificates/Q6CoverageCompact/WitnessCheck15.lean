import Paper2.Certificates.Q6CoverageCompact.WitnessCheck14

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_960_8 : checkRange checkTerminalAt 960 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_968_8 : checkRange checkTerminalAt 968 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_960_16 : checkRange checkTerminalAt 960 16 = true := checkRange_join checkTerminalAt 960 8 8 checkedTerminal_960_8 checkedTerminal_968_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_976_8 : checkRange checkTerminalAt 976 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_984_8 : checkRange checkTerminalAt 984 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_976_16 : checkRange checkTerminalAt 976 16 = true := checkRange_join checkTerminalAt 976 8 8 checkedTerminal_976_8 checkedTerminal_984_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_960_32 : checkRange checkTerminalAt 960 32 = true := checkRange_join checkTerminalAt 960 16 16 checkedTerminal_960_16 checkedTerminal_976_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_992_8 : checkRange checkTerminalAt 992 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1000_8 : checkRange checkTerminalAt 1000 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_992_16 : checkRange checkTerminalAt 992 16 = true := checkRange_join checkTerminalAt 992 8 8 checkedTerminal_992_8 checkedTerminal_1000_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1008_8 : checkRange checkTerminalAt 1008 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1016_8 : checkRange checkTerminalAt 1016 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1008_16 : checkRange checkTerminalAt 1008 16 = true := checkRange_join checkTerminalAt 1008 8 8 checkedTerminal_1008_8 checkedTerminal_1016_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_992_32 : checkRange checkTerminalAt 992 32 = true := checkRange_join checkTerminalAt 992 16 16 checkedTerminal_992_16 checkedTerminal_1008_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_960_64 : checkRange checkTerminalAt 960 64 = true := checkRange_join checkTerminalAt 960 32 32 checkedTerminal_960_32 checkedTerminal_992_32

end Paper2.Certificates.Q6.Coverage
