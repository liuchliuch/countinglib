import Paper2.Certificates.Q6CoverageCompact.WitnessCheck12

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_832_8 : checkRange checkTerminalAt 832 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_840_8 : checkRange checkTerminalAt 840 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_832_16 : checkRange checkTerminalAt 832 16 = true := checkRange_join checkTerminalAt 832 8 8 checkedTerminal_832_8 checkedTerminal_840_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_848_8 : checkRange checkTerminalAt 848 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_856_8 : checkRange checkTerminalAt 856 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_848_16 : checkRange checkTerminalAt 848 16 = true := checkRange_join checkTerminalAt 848 8 8 checkedTerminal_848_8 checkedTerminal_856_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_832_32 : checkRange checkTerminalAt 832 32 = true := checkRange_join checkTerminalAt 832 16 16 checkedTerminal_832_16 checkedTerminal_848_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_864_8 : checkRange checkTerminalAt 864 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_872_8 : checkRange checkTerminalAt 872 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_864_16 : checkRange checkTerminalAt 864 16 = true := checkRange_join checkTerminalAt 864 8 8 checkedTerminal_864_8 checkedTerminal_872_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_880_8 : checkRange checkTerminalAt 880 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_888_8 : checkRange checkTerminalAt 888 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_880_16 : checkRange checkTerminalAt 880 16 = true := checkRange_join checkTerminalAt 880 8 8 checkedTerminal_880_8 checkedTerminal_888_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_864_32 : checkRange checkTerminalAt 864 32 = true := checkRange_join checkTerminalAt 864 16 16 checkedTerminal_864_16 checkedTerminal_880_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_832_64 : checkRange checkTerminalAt 832 64 = true := checkRange_join checkTerminalAt 832 32 32 checkedTerminal_832_32 checkedTerminal_864_32

end Paper2.Certificates.Q6.Coverage
