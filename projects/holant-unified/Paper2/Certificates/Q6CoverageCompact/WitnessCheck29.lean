import Paper2.Certificates.Q6CoverageCompact.WitnessCheck28

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1856_6 : checkRange checkTerminalAt 1856 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1862_6 : checkRange checkTerminalAt 1862 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_1856_12 : checkRange checkTerminalAt 1856 12 = true := checkRange_join checkTerminalAt 1856 6 6 checkedTerminal_1856_6 checkedTerminal_1862_6

end Paper2.Certificates.Q6.Coverage
