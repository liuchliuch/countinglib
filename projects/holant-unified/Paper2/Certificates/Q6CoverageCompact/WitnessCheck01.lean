import Paper2.Certificates.Q6CoverageCompact.WitnessCheck00

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_64_8 : checkRange checkTerminalAt 64 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_72_8 : checkRange checkTerminalAt 72 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_64_16 : checkRange checkTerminalAt 64 16 = true := checkRange_join checkTerminalAt 64 8 8 checkedTerminal_64_8 checkedTerminal_72_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_80_8 : checkRange checkTerminalAt 80 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_88_8 : checkRange checkTerminalAt 88 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_80_16 : checkRange checkTerminalAt 80 16 = true := checkRange_join checkTerminalAt 80 8 8 checkedTerminal_80_8 checkedTerminal_88_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_64_32 : checkRange checkTerminalAt 64 32 = true := checkRange_join checkTerminalAt 64 16 16 checkedTerminal_64_16 checkedTerminal_80_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_96_8 : checkRange checkTerminalAt 96 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_104_8 : checkRange checkTerminalAt 104 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_96_16 : checkRange checkTerminalAt 96 16 = true := checkRange_join checkTerminalAt 96 8 8 checkedTerminal_96_8 checkedTerminal_104_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_112_8 : checkRange checkTerminalAt 112 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_120_8 : checkRange checkTerminalAt 120 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_112_16 : checkRange checkTerminalAt 112 16 = true := checkRange_join checkTerminalAt 112 8 8 checkedTerminal_112_8 checkedTerminal_120_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_96_32 : checkRange checkTerminalAt 96 32 = true := checkRange_join checkTerminalAt 96 16 16 checkedTerminal_96_16 checkedTerminal_112_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_64_64 : checkRange checkTerminalAt 64 64 = true := checkRange_join checkTerminalAt 64 32 32 checkedTerminal_64_32 checkedTerminal_96_32

end Paper2.Certificates.Q6.Coverage
