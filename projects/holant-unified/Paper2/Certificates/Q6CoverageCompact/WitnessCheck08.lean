import Paper2.Certificates.Q6CoverageCompact.WitnessCheck07

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_512_8 : checkRange checkTerminalAt 512 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_520_8 : checkRange checkTerminalAt 520 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_512_16 : checkRange checkTerminalAt 512 16 = true := checkRange_join checkTerminalAt 512 8 8 checkedTerminal_512_8 checkedTerminal_520_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_528_8 : checkRange checkTerminalAt 528 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_536_8 : checkRange checkTerminalAt 536 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_528_16 : checkRange checkTerminalAt 528 16 = true := checkRange_join checkTerminalAt 528 8 8 checkedTerminal_528_8 checkedTerminal_536_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_512_32 : checkRange checkTerminalAt 512 32 = true := checkRange_join checkTerminalAt 512 16 16 checkedTerminal_512_16 checkedTerminal_528_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_544_8 : checkRange checkTerminalAt 544 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_552_8 : checkRange checkTerminalAt 552 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_544_16 : checkRange checkTerminalAt 544 16 = true := checkRange_join checkTerminalAt 544 8 8 checkedTerminal_544_8 checkedTerminal_552_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_560_8 : checkRange checkTerminalAt 560 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_568_8 : checkRange checkTerminalAt 568 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_560_16 : checkRange checkTerminalAt 560 16 = true := checkRange_join checkTerminalAt 560 8 8 checkedTerminal_560_8 checkedTerminal_568_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_544_32 : checkRange checkTerminalAt 544 32 = true := checkRange_join checkTerminalAt 544 16 16 checkedTerminal_544_16 checkedTerminal_560_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_512_64 : checkRange checkTerminalAt 512 64 = true := checkRange_join checkTerminalAt 512 32 32 checkedTerminal_512_32 checkedTerminal_544_32

end Paper2.Certificates.Q6.Coverage
