import Paper2.Certificates.Q6CoverageCompact.WitnessCheck19

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1280_8 : checkRange checkTerminalAt 1280 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1288_8 : checkRange checkTerminalAt 1288 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1280_16 : checkRange checkTerminalAt 1280 16 = true := checkRange_join checkTerminalAt 1280 8 8 checkedTerminal_1280_8 checkedTerminal_1288_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1296_8 : checkRange checkTerminalAt 1296 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1304_8 : checkRange checkTerminalAt 1304 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1296_16 : checkRange checkTerminalAt 1296 16 = true := checkRange_join checkTerminalAt 1296 8 8 checkedTerminal_1296_8 checkedTerminal_1304_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1280_32 : checkRange checkTerminalAt 1280 32 = true := checkRange_join checkTerminalAt 1280 16 16 checkedTerminal_1280_16 checkedTerminal_1296_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1312_8 : checkRange checkTerminalAt 1312 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1320_8 : checkRange checkTerminalAt 1320 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1312_16 : checkRange checkTerminalAt 1312 16 = true := checkRange_join checkTerminalAt 1312 8 8 checkedTerminal_1312_8 checkedTerminal_1320_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1328_8 : checkRange checkTerminalAt 1328 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1336_8 : checkRange checkTerminalAt 1336 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1328_16 : checkRange checkTerminalAt 1328 16 = true := checkRange_join checkTerminalAt 1328 8 8 checkedTerminal_1328_8 checkedTerminal_1336_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1312_32 : checkRange checkTerminalAt 1312 32 = true := checkRange_join checkTerminalAt 1312 16 16 checkedTerminal_1312_16 checkedTerminal_1328_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1280_64 : checkRange checkTerminalAt 1280 64 = true := checkRange_join checkTerminalAt 1280 32 32 checkedTerminal_1280_32 checkedTerminal_1312_32

end Paper2.Certificates.Q6.Coverage
