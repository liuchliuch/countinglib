import Paper2.Certificates.Q6CoverageCompact.WitnessCheck03

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_256_8 : checkRange checkTerminalAt 256 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_264_8 : checkRange checkTerminalAt 264 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_256_16 : checkRange checkTerminalAt 256 16 = true := checkRange_join checkTerminalAt 256 8 8 checkedTerminal_256_8 checkedTerminal_264_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_272_8 : checkRange checkTerminalAt 272 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_280_8 : checkRange checkTerminalAt 280 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_272_16 : checkRange checkTerminalAt 272 16 = true := checkRange_join checkTerminalAt 272 8 8 checkedTerminal_272_8 checkedTerminal_280_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_256_32 : checkRange checkTerminalAt 256 32 = true := checkRange_join checkTerminalAt 256 16 16 checkedTerminal_256_16 checkedTerminal_272_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_288_8 : checkRange checkTerminalAt 288 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_296_8 : checkRange checkTerminalAt 296 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_288_16 : checkRange checkTerminalAt 288 16 = true := checkRange_join checkTerminalAt 288 8 8 checkedTerminal_288_8 checkedTerminal_296_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_304_8 : checkRange checkTerminalAt 304 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_312_8 : checkRange checkTerminalAt 312 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_304_16 : checkRange checkTerminalAt 304 16 = true := checkRange_join checkTerminalAt 304 8 8 checkedTerminal_304_8 checkedTerminal_312_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_288_32 : checkRange checkTerminalAt 288 32 = true := checkRange_join checkTerminalAt 288 16 16 checkedTerminal_288_16 checkedTerminal_304_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_256_64 : checkRange checkTerminalAt 256 64 = true := checkRange_join checkTerminalAt 256 32 32 checkedTerminal_256_32 checkedTerminal_288_32

end Paper2.Certificates.Q6.Coverage
