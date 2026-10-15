import Paper2.Certificates.Q6CoverageCompact.WitnessCheck15

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1024_8 : checkRange checkTerminalAt 1024 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1032_8 : checkRange checkTerminalAt 1032 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1024_16 : checkRange checkTerminalAt 1024 16 = true := checkRange_join checkTerminalAt 1024 8 8 checkedTerminal_1024_8 checkedTerminal_1032_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1040_8 : checkRange checkTerminalAt 1040 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1048_8 : checkRange checkTerminalAt 1048 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1040_16 : checkRange checkTerminalAt 1040 16 = true := checkRange_join checkTerminalAt 1040 8 8 checkedTerminal_1040_8 checkedTerminal_1048_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1024_32 : checkRange checkTerminalAt 1024 32 = true := checkRange_join checkTerminalAt 1024 16 16 checkedTerminal_1024_16 checkedTerminal_1040_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1056_8 : checkRange checkTerminalAt 1056 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1064_8 : checkRange checkTerminalAt 1064 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1056_16 : checkRange checkTerminalAt 1056 16 = true := checkRange_join checkTerminalAt 1056 8 8 checkedTerminal_1056_8 checkedTerminal_1064_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1072_8 : checkRange checkTerminalAt 1072 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1080_8 : checkRange checkTerminalAt 1080 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1072_16 : checkRange checkTerminalAt 1072 16 = true := checkRange_join checkTerminalAt 1072 8 8 checkedTerminal_1072_8 checkedTerminal_1080_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1056_32 : checkRange checkTerminalAt 1056 32 = true := checkRange_join checkTerminalAt 1056 16 16 checkedTerminal_1056_16 checkedTerminal_1072_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1024_64 : checkRange checkTerminalAt 1024 64 = true := checkRange_join checkTerminalAt 1024 32 32 checkedTerminal_1024_32 checkedTerminal_1056_32

end Paper2.Certificates.Q6.Coverage
