import Paper2.Certificates.Q6CoverageCompact.WitnessCheck22

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1472_8 : checkRange checkTerminalAt 1472 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1480_8 : checkRange checkTerminalAt 1480 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1472_16 : checkRange checkTerminalAt 1472 16 = true := checkRange_join checkTerminalAt 1472 8 8 checkedTerminal_1472_8 checkedTerminal_1480_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1488_8 : checkRange checkTerminalAt 1488 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1496_8 : checkRange checkTerminalAt 1496 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1488_16 : checkRange checkTerminalAt 1488 16 = true := checkRange_join checkTerminalAt 1488 8 8 checkedTerminal_1488_8 checkedTerminal_1496_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1472_32 : checkRange checkTerminalAt 1472 32 = true := checkRange_join checkTerminalAt 1472 16 16 checkedTerminal_1472_16 checkedTerminal_1488_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1504_8 : checkRange checkTerminalAt 1504 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1512_8 : checkRange checkTerminalAt 1512 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1504_16 : checkRange checkTerminalAt 1504 16 = true := checkRange_join checkTerminalAt 1504 8 8 checkedTerminal_1504_8 checkedTerminal_1512_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1520_8 : checkRange checkTerminalAt 1520 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1528_8 : checkRange checkTerminalAt 1528 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1520_16 : checkRange checkTerminalAt 1520 16 = true := checkRange_join checkTerminalAt 1520 8 8 checkedTerminal_1520_8 checkedTerminal_1528_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1504_32 : checkRange checkTerminalAt 1504 32 = true := checkRange_join checkTerminalAt 1504 16 16 checkedTerminal_1504_16 checkedTerminal_1520_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1472_64 : checkRange checkTerminalAt 1472 64 = true := checkRange_join checkTerminalAt 1472 32 32 checkedTerminal_1472_32 checkedTerminal_1504_32

end Paper2.Certificates.Q6.Coverage
