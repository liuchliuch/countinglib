import Paper2.Certificates.Q6CoverageCompact.WitnessCheck26

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1728_8 : checkRange checkTerminalAt 1728 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1736_8 : checkRange checkTerminalAt 1736 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1728_16 : checkRange checkTerminalAt 1728 16 = true := checkRange_join checkTerminalAt 1728 8 8 checkedTerminal_1728_8 checkedTerminal_1736_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1744_8 : checkRange checkTerminalAt 1744 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1752_8 : checkRange checkTerminalAt 1752 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1744_16 : checkRange checkTerminalAt 1744 16 = true := checkRange_join checkTerminalAt 1744 8 8 checkedTerminal_1744_8 checkedTerminal_1752_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1728_32 : checkRange checkTerminalAt 1728 32 = true := checkRange_join checkTerminalAt 1728 16 16 checkedTerminal_1728_16 checkedTerminal_1744_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1760_8 : checkRange checkTerminalAt 1760 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1768_8 : checkRange checkTerminalAt 1768 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1760_16 : checkRange checkTerminalAt 1760 16 = true := checkRange_join checkTerminalAt 1760 8 8 checkedTerminal_1760_8 checkedTerminal_1768_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1776_8 : checkRange checkTerminalAt 1776 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1784_8 : checkRange checkTerminalAt 1784 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1776_16 : checkRange checkTerminalAt 1776 16 = true := checkRange_join checkTerminalAt 1776 8 8 checkedTerminal_1776_8 checkedTerminal_1784_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1760_32 : checkRange checkTerminalAt 1760 32 = true := checkRange_join checkTerminalAt 1760 16 16 checkedTerminal_1760_16 checkedTerminal_1776_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1728_64 : checkRange checkTerminalAt 1728 64 = true := checkRange_join checkTerminalAt 1728 32 32 checkedTerminal_1728_32 checkedTerminal_1760_32

end Paper2.Certificates.Q6.Coverage
