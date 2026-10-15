import Paper2.Certificates.Q6CoverageCompact.WitnessCheck20

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1344_8 : checkRange checkTerminalAt 1344 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1352_8 : checkRange checkTerminalAt 1352 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1344_16 : checkRange checkTerminalAt 1344 16 = true := checkRange_join checkTerminalAt 1344 8 8 checkedTerminal_1344_8 checkedTerminal_1352_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1360_8 : checkRange checkTerminalAt 1360 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1368_8 : checkRange checkTerminalAt 1368 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1360_16 : checkRange checkTerminalAt 1360 16 = true := checkRange_join checkTerminalAt 1360 8 8 checkedTerminal_1360_8 checkedTerminal_1368_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1344_32 : checkRange checkTerminalAt 1344 32 = true := checkRange_join checkTerminalAt 1344 16 16 checkedTerminal_1344_16 checkedTerminal_1360_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1376_8 : checkRange checkTerminalAt 1376 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1384_8 : checkRange checkTerminalAt 1384 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1376_16 : checkRange checkTerminalAt 1376 16 = true := checkRange_join checkTerminalAt 1376 8 8 checkedTerminal_1376_8 checkedTerminal_1384_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1392_8 : checkRange checkTerminalAt 1392 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1400_8 : checkRange checkTerminalAt 1400 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1392_16 : checkRange checkTerminalAt 1392 16 = true := checkRange_join checkTerminalAt 1392 8 8 checkedTerminal_1392_8 checkedTerminal_1400_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1376_32 : checkRange checkTerminalAt 1376 32 = true := checkRange_join checkTerminalAt 1376 16 16 checkedTerminal_1376_16 checkedTerminal_1392_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1344_64 : checkRange checkTerminalAt 1344 64 = true := checkRange_join checkTerminalAt 1344 32 32 checkedTerminal_1344_32 checkedTerminal_1376_32

end Paper2.Certificates.Q6.Coverage
