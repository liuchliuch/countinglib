import Paper2.Certificates.Q6CoverageCompact.WitnessCheck21

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1408_8 : checkRange checkTerminalAt 1408 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1416_8 : checkRange checkTerminalAt 1416 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1408_16 : checkRange checkTerminalAt 1408 16 = true := checkRange_join checkTerminalAt 1408 8 8 checkedTerminal_1408_8 checkedTerminal_1416_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1424_8 : checkRange checkTerminalAt 1424 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1432_8 : checkRange checkTerminalAt 1432 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1424_16 : checkRange checkTerminalAt 1424 16 = true := checkRange_join checkTerminalAt 1424 8 8 checkedTerminal_1424_8 checkedTerminal_1432_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1408_32 : checkRange checkTerminalAt 1408 32 = true := checkRange_join checkTerminalAt 1408 16 16 checkedTerminal_1408_16 checkedTerminal_1424_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1440_8 : checkRange checkTerminalAt 1440 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1448_8 : checkRange checkTerminalAt 1448 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1440_16 : checkRange checkTerminalAt 1440 16 = true := checkRange_join checkTerminalAt 1440 8 8 checkedTerminal_1440_8 checkedTerminal_1448_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1456_8 : checkRange checkTerminalAt 1456 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1464_8 : checkRange checkTerminalAt 1464 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1456_16 : checkRange checkTerminalAt 1456 16 = true := checkRange_join checkTerminalAt 1456 8 8 checkedTerminal_1456_8 checkedTerminal_1464_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1440_32 : checkRange checkTerminalAt 1440 32 = true := checkRange_join checkTerminalAt 1440 16 16 checkedTerminal_1440_16 checkedTerminal_1456_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1408_64 : checkRange checkTerminalAt 1408 64 = true := checkRange_join checkTerminalAt 1408 32 32 checkedTerminal_1408_32 checkedTerminal_1440_32

end Paper2.Certificates.Q6.Coverage
