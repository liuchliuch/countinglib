import Paper2.Certificates.Q6CoverageCompact.WitnessCheck25

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1664_8 : checkRange checkTerminalAt 1664 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1672_8 : checkRange checkTerminalAt 1672 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1664_16 : checkRange checkTerminalAt 1664 16 = true := checkRange_join checkTerminalAt 1664 8 8 checkedTerminal_1664_8 checkedTerminal_1672_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1680_8 : checkRange checkTerminalAt 1680 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1688_8 : checkRange checkTerminalAt 1688 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1680_16 : checkRange checkTerminalAt 1680 16 = true := checkRange_join checkTerminalAt 1680 8 8 checkedTerminal_1680_8 checkedTerminal_1688_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1664_32 : checkRange checkTerminalAt 1664 32 = true := checkRange_join checkTerminalAt 1664 16 16 checkedTerminal_1664_16 checkedTerminal_1680_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1696_8 : checkRange checkTerminalAt 1696 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1704_8 : checkRange checkTerminalAt 1704 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1696_16 : checkRange checkTerminalAt 1696 16 = true := checkRange_join checkTerminalAt 1696 8 8 checkedTerminal_1696_8 checkedTerminal_1704_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1712_8 : checkRange checkTerminalAt 1712 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1720_8 : checkRange checkTerminalAt 1720 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1712_16 : checkRange checkTerminalAt 1712 16 = true := checkRange_join checkTerminalAt 1712 8 8 checkedTerminal_1712_8 checkedTerminal_1720_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1696_32 : checkRange checkTerminalAt 1696 32 = true := checkRange_join checkTerminalAt 1696 16 16 checkedTerminal_1696_16 checkedTerminal_1712_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1664_64 : checkRange checkTerminalAt 1664 64 = true := checkRange_join checkTerminalAt 1664 32 32 checkedTerminal_1664_32 checkedTerminal_1696_32

end Paper2.Certificates.Q6.Coverage
