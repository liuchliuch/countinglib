import Paper2.Certificates.Q6CoverageCompact.WitnessCheck05

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_384_8 : checkRange checkTerminalAt 384 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_392_8 : checkRange checkTerminalAt 392 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_384_16 : checkRange checkTerminalAt 384 16 = true := checkRange_join checkTerminalAt 384 8 8 checkedTerminal_384_8 checkedTerminal_392_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_400_8 : checkRange checkTerminalAt 400 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_408_8 : checkRange checkTerminalAt 408 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_400_16 : checkRange checkTerminalAt 400 16 = true := checkRange_join checkTerminalAt 400 8 8 checkedTerminal_400_8 checkedTerminal_408_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_384_32 : checkRange checkTerminalAt 384 32 = true := checkRange_join checkTerminalAt 384 16 16 checkedTerminal_384_16 checkedTerminal_400_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_416_8 : checkRange checkTerminalAt 416 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_424_8 : checkRange checkTerminalAt 424 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_416_16 : checkRange checkTerminalAt 416 16 = true := checkRange_join checkTerminalAt 416 8 8 checkedTerminal_416_8 checkedTerminal_424_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_432_8 : checkRange checkTerminalAt 432 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_440_8 : checkRange checkTerminalAt 440 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_432_16 : checkRange checkTerminalAt 432 16 = true := checkRange_join checkTerminalAt 432 8 8 checkedTerminal_432_8 checkedTerminal_440_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_416_32 : checkRange checkTerminalAt 416 32 = true := checkRange_join checkTerminalAt 416 16 16 checkedTerminal_416_16 checkedTerminal_432_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_384_64 : checkRange checkTerminalAt 384 64 = true := checkRange_join checkTerminalAt 384 32 32 checkedTerminal_384_32 checkedTerminal_416_32

end Paper2.Certificates.Q6.Coverage
