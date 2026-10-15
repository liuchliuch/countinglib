import Paper2.Certificates.Q6CoverageCompact.WitnessCheck24

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1600_8 : checkRange checkTerminalAt 1600 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1608_8 : checkRange checkTerminalAt 1608 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1600_16 : checkRange checkTerminalAt 1600 16 = true := checkRange_join checkTerminalAt 1600 8 8 checkedTerminal_1600_8 checkedTerminal_1608_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1616_8 : checkRange checkTerminalAt 1616 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1624_8 : checkRange checkTerminalAt 1624 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1616_16 : checkRange checkTerminalAt 1616 16 = true := checkRange_join checkTerminalAt 1616 8 8 checkedTerminal_1616_8 checkedTerminal_1624_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1600_32 : checkRange checkTerminalAt 1600 32 = true := checkRange_join checkTerminalAt 1600 16 16 checkedTerminal_1600_16 checkedTerminal_1616_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1632_8 : checkRange checkTerminalAt 1632 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1640_8 : checkRange checkTerminalAt 1640 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1632_16 : checkRange checkTerminalAt 1632 16 = true := checkRange_join checkTerminalAt 1632 8 8 checkedTerminal_1632_8 checkedTerminal_1640_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1648_8 : checkRange checkTerminalAt 1648 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1656_8 : checkRange checkTerminalAt 1656 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1648_16 : checkRange checkTerminalAt 1648 16 = true := checkRange_join checkTerminalAt 1648 8 8 checkedTerminal_1648_8 checkedTerminal_1656_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1632_32 : checkRange checkTerminalAt 1632 32 = true := checkRange_join checkTerminalAt 1632 16 16 checkedTerminal_1632_16 checkedTerminal_1648_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1600_64 : checkRange checkTerminalAt 1600 64 = true := checkRange_join checkTerminalAt 1600 32 32 checkedTerminal_1600_32 checkedTerminal_1632_32

end Paper2.Certificates.Q6.Coverage
