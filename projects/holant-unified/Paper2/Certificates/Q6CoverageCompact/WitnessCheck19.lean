import Paper2.Certificates.Q6CoverageCompact.WitnessCheck18

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1216_8 : checkRange checkTerminalAt 1216 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1224_8 : checkRange checkTerminalAt 1224 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1216_16 : checkRange checkTerminalAt 1216 16 = true := checkRange_join checkTerminalAt 1216 8 8 checkedTerminal_1216_8 checkedTerminal_1224_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1232_8 : checkRange checkTerminalAt 1232 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1240_8 : checkRange checkTerminalAt 1240 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1232_16 : checkRange checkTerminalAt 1232 16 = true := checkRange_join checkTerminalAt 1232 8 8 checkedTerminal_1232_8 checkedTerminal_1240_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1216_32 : checkRange checkTerminalAt 1216 32 = true := checkRange_join checkTerminalAt 1216 16 16 checkedTerminal_1216_16 checkedTerminal_1232_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1248_8 : checkRange checkTerminalAt 1248 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1256_8 : checkRange checkTerminalAt 1256 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1248_16 : checkRange checkTerminalAt 1248 16 = true := checkRange_join checkTerminalAt 1248 8 8 checkedTerminal_1248_8 checkedTerminal_1256_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1264_8 : checkRange checkTerminalAt 1264 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1272_8 : checkRange checkTerminalAt 1272 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1264_16 : checkRange checkTerminalAt 1264 16 = true := checkRange_join checkTerminalAt 1264 8 8 checkedTerminal_1264_8 checkedTerminal_1272_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1248_32 : checkRange checkTerminalAt 1248 32 = true := checkRange_join checkTerminalAt 1248 16 16 checkedTerminal_1248_16 checkedTerminal_1264_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1216_64 : checkRange checkTerminalAt 1216 64 = true := checkRange_join checkTerminalAt 1216 32 32 checkedTerminal_1216_32 checkedTerminal_1248_32

end Paper2.Certificates.Q6.Coverage
