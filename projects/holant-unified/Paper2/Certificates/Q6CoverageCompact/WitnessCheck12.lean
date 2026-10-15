import Paper2.Certificates.Q6CoverageCompact.WitnessCheck11

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_768_8 : checkRange checkTerminalAt 768 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_776_8 : checkRange checkTerminalAt 776 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_768_16 : checkRange checkTerminalAt 768 16 = true := checkRange_join checkTerminalAt 768 8 8 checkedTerminal_768_8 checkedTerminal_776_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_784_8 : checkRange checkTerminalAt 784 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_792_8 : checkRange checkTerminalAt 792 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_784_16 : checkRange checkTerminalAt 784 16 = true := checkRange_join checkTerminalAt 784 8 8 checkedTerminal_784_8 checkedTerminal_792_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_768_32 : checkRange checkTerminalAt 768 32 = true := checkRange_join checkTerminalAt 768 16 16 checkedTerminal_768_16 checkedTerminal_784_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_800_8 : checkRange checkTerminalAt 800 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_808_8 : checkRange checkTerminalAt 808 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_800_16 : checkRange checkTerminalAt 800 16 = true := checkRange_join checkTerminalAt 800 8 8 checkedTerminal_800_8 checkedTerminal_808_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_816_8 : checkRange checkTerminalAt 816 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_824_8 : checkRange checkTerminalAt 824 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_816_16 : checkRange checkTerminalAt 816 16 = true := checkRange_join checkTerminalAt 816 8 8 checkedTerminal_816_8 checkedTerminal_824_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_800_32 : checkRange checkTerminalAt 800 32 = true := checkRange_join checkTerminalAt 800 16 16 checkedTerminal_800_16 checkedTerminal_816_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_768_64 : checkRange checkTerminalAt 768 64 = true := checkRange_join checkTerminalAt 768 32 32 checkedTerminal_768_32 checkedTerminal_800_32

end Paper2.Certificates.Q6.Coverage
