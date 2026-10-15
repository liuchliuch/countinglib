import Paper2.Certificates.Q6CoverageCompact.WitnessCheck09

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_640_8 : checkRange checkTerminalAt 640 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_648_8 : checkRange checkTerminalAt 648 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_640_16 : checkRange checkTerminalAt 640 16 = true := checkRange_join checkTerminalAt 640 8 8 checkedTerminal_640_8 checkedTerminal_648_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_656_8 : checkRange checkTerminalAt 656 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_664_8 : checkRange checkTerminalAt 664 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_656_16 : checkRange checkTerminalAt 656 16 = true := checkRange_join checkTerminalAt 656 8 8 checkedTerminal_656_8 checkedTerminal_664_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_640_32 : checkRange checkTerminalAt 640 32 = true := checkRange_join checkTerminalAt 640 16 16 checkedTerminal_640_16 checkedTerminal_656_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_672_8 : checkRange checkTerminalAt 672 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_680_8 : checkRange checkTerminalAt 680 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_672_16 : checkRange checkTerminalAt 672 16 = true := checkRange_join checkTerminalAt 672 8 8 checkedTerminal_672_8 checkedTerminal_680_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_688_8 : checkRange checkTerminalAt 688 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_696_8 : checkRange checkTerminalAt 696 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_688_16 : checkRange checkTerminalAt 688 16 = true := checkRange_join checkTerminalAt 688 8 8 checkedTerminal_688_8 checkedTerminal_696_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_672_32 : checkRange checkTerminalAt 672 32 = true := checkRange_join checkTerminalAt 672 16 16 checkedTerminal_672_16 checkedTerminal_688_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_640_64 : checkRange checkTerminalAt 640 64 = true := checkRange_join checkTerminalAt 640 32 32 checkedTerminal_640_32 checkedTerminal_672_32

end Paper2.Certificates.Q6.Coverage
