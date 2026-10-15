import Paper2.Certificates.Q6CoverageCompact.WitnessCheck04

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_320_8 : checkRange checkTerminalAt 320 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_328_8 : checkRange checkTerminalAt 328 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_320_16 : checkRange checkTerminalAt 320 16 = true := checkRange_join checkTerminalAt 320 8 8 checkedTerminal_320_8 checkedTerminal_328_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_336_8 : checkRange checkTerminalAt 336 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_344_8 : checkRange checkTerminalAt 344 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_336_16 : checkRange checkTerminalAt 336 16 = true := checkRange_join checkTerminalAt 336 8 8 checkedTerminal_336_8 checkedTerminal_344_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_320_32 : checkRange checkTerminalAt 320 32 = true := checkRange_join checkTerminalAt 320 16 16 checkedTerminal_320_16 checkedTerminal_336_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_352_8 : checkRange checkTerminalAt 352 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_360_8 : checkRange checkTerminalAt 360 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_352_16 : checkRange checkTerminalAt 352 16 = true := checkRange_join checkTerminalAt 352 8 8 checkedTerminal_352_8 checkedTerminal_360_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_368_8 : checkRange checkTerminalAt 368 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_376_8 : checkRange checkTerminalAt 376 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_368_16 : checkRange checkTerminalAt 368 16 = true := checkRange_join checkTerminalAt 368 8 8 checkedTerminal_368_8 checkedTerminal_376_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_352_32 : checkRange checkTerminalAt 352 32 = true := checkRange_join checkTerminalAt 352 16 16 checkedTerminal_352_16 checkedTerminal_368_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_320_64 : checkRange checkTerminalAt 320 64 = true := checkRange_join checkTerminalAt 320 32 32 checkedTerminal_320_32 checkedTerminal_352_32

end Paper2.Certificates.Q6.Coverage
