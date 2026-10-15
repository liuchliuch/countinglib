import Paper2.Certificates.Q6CoverageCompact.WitnessCheck27

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1792_8 : checkRange checkTerminalAt 1792 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1800_8 : checkRange checkTerminalAt 1800 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1792_16 : checkRange checkTerminalAt 1792 16 = true := checkRange_join checkTerminalAt 1792 8 8 checkedTerminal_1792_8 checkedTerminal_1800_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1808_8 : checkRange checkTerminalAt 1808 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1816_8 : checkRange checkTerminalAt 1816 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1808_16 : checkRange checkTerminalAt 1808 16 = true := checkRange_join checkTerminalAt 1808 8 8 checkedTerminal_1808_8 checkedTerminal_1816_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1792_32 : checkRange checkTerminalAt 1792 32 = true := checkRange_join checkTerminalAt 1792 16 16 checkedTerminal_1792_16 checkedTerminal_1808_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1824_8 : checkRange checkTerminalAt 1824 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1832_8 : checkRange checkTerminalAt 1832 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1824_16 : checkRange checkTerminalAt 1824 16 = true := checkRange_join checkTerminalAt 1824 8 8 checkedTerminal_1824_8 checkedTerminal_1832_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1840_8 : checkRange checkTerminalAt 1840 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1848_8 : checkRange checkTerminalAt 1848 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1840_16 : checkRange checkTerminalAt 1840 16 = true := checkRange_join checkTerminalAt 1840 8 8 checkedTerminal_1840_8 checkedTerminal_1848_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1824_32 : checkRange checkTerminalAt 1824 32 = true := checkRange_join checkTerminalAt 1824 16 16 checkedTerminal_1824_16 checkedTerminal_1840_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1792_64 : checkRange checkTerminalAt 1792 64 = true := checkRange_join checkTerminalAt 1792 32 32 checkedTerminal_1792_32 checkedTerminal_1824_32

end Paper2.Certificates.Q6.Coverage
