import Paper2.Certificates.Q6CoverageCompact.WitnessCheck02

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_192_8 : checkRange checkTerminalAt 192 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_200_8 : checkRange checkTerminalAt 200 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_192_16 : checkRange checkTerminalAt 192 16 = true := checkRange_join checkTerminalAt 192 8 8 checkedTerminal_192_8 checkedTerminal_200_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_208_8 : checkRange checkTerminalAt 208 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_216_8 : checkRange checkTerminalAt 216 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_208_16 : checkRange checkTerminalAt 208 16 = true := checkRange_join checkTerminalAt 208 8 8 checkedTerminal_208_8 checkedTerminal_216_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_192_32 : checkRange checkTerminalAt 192 32 = true := checkRange_join checkTerminalAt 192 16 16 checkedTerminal_192_16 checkedTerminal_208_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_224_8 : checkRange checkTerminalAt 224 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_232_8 : checkRange checkTerminalAt 232 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_224_16 : checkRange checkTerminalAt 224 16 = true := checkRange_join checkTerminalAt 224 8 8 checkedTerminal_224_8 checkedTerminal_232_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_240_8 : checkRange checkTerminalAt 240 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_248_8 : checkRange checkTerminalAt 248 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_240_16 : checkRange checkTerminalAt 240 16 = true := checkRange_join checkTerminalAt 240 8 8 checkedTerminal_240_8 checkedTerminal_248_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_224_32 : checkRange checkTerminalAt 224 32 = true := checkRange_join checkTerminalAt 224 16 16 checkedTerminal_224_16 checkedTerminal_240_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_192_64 : checkRange checkTerminalAt 192 64 = true := checkRange_join checkTerminalAt 192 32 32 checkedTerminal_192_32 checkedTerminal_224_32

end Paper2.Certificates.Q6.Coverage
