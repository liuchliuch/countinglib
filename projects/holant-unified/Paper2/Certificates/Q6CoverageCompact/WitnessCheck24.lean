import Paper2.Certificates.Q6CoverageCompact.WitnessCheck23

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1536_8 : checkRange checkTerminalAt 1536 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1544_8 : checkRange checkTerminalAt 1544 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1536_16 : checkRange checkTerminalAt 1536 16 = true := checkRange_join checkTerminalAt 1536 8 8 checkedTerminal_1536_8 checkedTerminal_1544_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1552_8 : checkRange checkTerminalAt 1552 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1560_8 : checkRange checkTerminalAt 1560 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1552_16 : checkRange checkTerminalAt 1552 16 = true := checkRange_join checkTerminalAt 1552 8 8 checkedTerminal_1552_8 checkedTerminal_1560_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1536_32 : checkRange checkTerminalAt 1536 32 = true := checkRange_join checkTerminalAt 1536 16 16 checkedTerminal_1536_16 checkedTerminal_1552_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1568_8 : checkRange checkTerminalAt 1568 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1576_8 : checkRange checkTerminalAt 1576 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1568_16 : checkRange checkTerminalAt 1568 16 = true := checkRange_join checkTerminalAt 1568 8 8 checkedTerminal_1568_8 checkedTerminal_1576_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1584_8 : checkRange checkTerminalAt 1584 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1592_8 : checkRange checkTerminalAt 1592 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1584_16 : checkRange checkTerminalAt 1584 16 = true := checkRange_join checkTerminalAt 1584 8 8 checkedTerminal_1584_8 checkedTerminal_1592_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1568_32 : checkRange checkTerminalAt 1568 32 = true := checkRange_join checkTerminalAt 1568 16 16 checkedTerminal_1568_16 checkedTerminal_1584_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1536_64 : checkRange checkTerminalAt 1536 64 = true := checkRange_join checkTerminalAt 1536 32 32 checkedTerminal_1536_32 checkedTerminal_1568_32

end Paper2.Certificates.Q6.Coverage
