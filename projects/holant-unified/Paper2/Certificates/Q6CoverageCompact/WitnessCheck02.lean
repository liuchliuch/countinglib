import Paper2.Certificates.Q6CoverageCompact.WitnessCheck01

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_128_8 : checkRange checkTerminalAt 128 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_136_8 : checkRange checkTerminalAt 136 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_128_16 : checkRange checkTerminalAt 128 16 = true := checkRange_join checkTerminalAt 128 8 8 checkedTerminal_128_8 checkedTerminal_136_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_144_8 : checkRange checkTerminalAt 144 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_152_8 : checkRange checkTerminalAt 152 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_144_16 : checkRange checkTerminalAt 144 16 = true := checkRange_join checkTerminalAt 144 8 8 checkedTerminal_144_8 checkedTerminal_152_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_128_32 : checkRange checkTerminalAt 128 32 = true := checkRange_join checkTerminalAt 128 16 16 checkedTerminal_128_16 checkedTerminal_144_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_160_8 : checkRange checkTerminalAt 160 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_168_8 : checkRange checkTerminalAt 168 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_160_16 : checkRange checkTerminalAt 160 16 = true := checkRange_join checkTerminalAt 160 8 8 checkedTerminal_160_8 checkedTerminal_168_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_176_8 : checkRange checkTerminalAt 176 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_184_8 : checkRange checkTerminalAt 184 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_176_16 : checkRange checkTerminalAt 176 16 = true := checkRange_join checkTerminalAt 176 8 8 checkedTerminal_176_8 checkedTerminal_184_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_160_32 : checkRange checkTerminalAt 160 32 = true := checkRange_join checkTerminalAt 160 16 16 checkedTerminal_160_16 checkedTerminal_176_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_128_64 : checkRange checkTerminalAt 128 64 = true := checkRange_join checkTerminalAt 128 32 32 checkedTerminal_128_32 checkedTerminal_160_32

end Paper2.Certificates.Q6.Coverage
