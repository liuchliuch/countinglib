import Paper2.Certificates.Q6CoverageCompact.WitnessCheck08

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_576_8 : checkRange checkTerminalAt 576 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_584_8 : checkRange checkTerminalAt 584 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_576_16 : checkRange checkTerminalAt 576 16 = true := checkRange_join checkTerminalAt 576 8 8 checkedTerminal_576_8 checkedTerminal_584_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_592_8 : checkRange checkTerminalAt 592 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_600_8 : checkRange checkTerminalAt 600 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_592_16 : checkRange checkTerminalAt 592 16 = true := checkRange_join checkTerminalAt 592 8 8 checkedTerminal_592_8 checkedTerminal_600_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_576_32 : checkRange checkTerminalAt 576 32 = true := checkRange_join checkTerminalAt 576 16 16 checkedTerminal_576_16 checkedTerminal_592_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_608_8 : checkRange checkTerminalAt 608 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_616_8 : checkRange checkTerminalAt 616 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_608_16 : checkRange checkTerminalAt 608 16 = true := checkRange_join checkTerminalAt 608 8 8 checkedTerminal_608_8 checkedTerminal_616_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_624_8 : checkRange checkTerminalAt 624 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_632_8 : checkRange checkTerminalAt 632 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_624_16 : checkRange checkTerminalAt 624 16 = true := checkRange_join checkTerminalAt 624 8 8 checkedTerminal_624_8 checkedTerminal_632_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_608_32 : checkRange checkTerminalAt 608 32 = true := checkRange_join checkTerminalAt 608 16 16 checkedTerminal_608_16 checkedTerminal_624_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_576_64 : checkRange checkTerminalAt 576 64 = true := checkRange_join checkTerminalAt 576 32 32 checkedTerminal_576_32 checkedTerminal_608_32

end Paper2.Certificates.Q6.Coverage
