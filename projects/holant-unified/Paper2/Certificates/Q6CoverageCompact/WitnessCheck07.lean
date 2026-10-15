import Paper2.Certificates.Q6CoverageCompact.WitnessCheck06

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_448_8 : checkRange checkTerminalAt 448 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_456_8 : checkRange checkTerminalAt 456 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_448_16 : checkRange checkTerminalAt 448 16 = true := checkRange_join checkTerminalAt 448 8 8 checkedTerminal_448_8 checkedTerminal_456_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_464_8 : checkRange checkTerminalAt 464 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_472_8 : checkRange checkTerminalAt 472 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_464_16 : checkRange checkTerminalAt 464 16 = true := checkRange_join checkTerminalAt 464 8 8 checkedTerminal_464_8 checkedTerminal_472_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_448_32 : checkRange checkTerminalAt 448 32 = true := checkRange_join checkTerminalAt 448 16 16 checkedTerminal_448_16 checkedTerminal_464_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_480_8 : checkRange checkTerminalAt 480 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_488_8 : checkRange checkTerminalAt 488 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_480_16 : checkRange checkTerminalAt 480 16 = true := checkRange_join checkTerminalAt 480 8 8 checkedTerminal_480_8 checkedTerminal_488_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_496_8 : checkRange checkTerminalAt 496 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_504_8 : checkRange checkTerminalAt 504 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_496_16 : checkRange checkTerminalAt 496 16 = true := checkRange_join checkTerminalAt 496 8 8 checkedTerminal_496_8 checkedTerminal_504_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_480_32 : checkRange checkTerminalAt 480 32 = true := checkRange_join checkTerminalAt 480 16 16 checkedTerminal_480_16 checkedTerminal_496_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_448_64 : checkRange checkTerminalAt 448 64 = true := checkRange_join checkTerminalAt 448 32 32 checkedTerminal_448_32 checkedTerminal_480_32

end Paper2.Certificates.Q6.Coverage
