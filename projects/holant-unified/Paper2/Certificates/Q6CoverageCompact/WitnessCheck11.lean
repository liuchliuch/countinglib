import Paper2.Certificates.Q6CoverageCompact.WitnessCheck10

namespace Paper2.Certificates.Q6.Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_704_8 : checkRange checkTerminalAt 704 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_712_8 : checkRange checkTerminalAt 712 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_704_16 : checkRange checkTerminalAt 704 16 = true := checkRange_join checkTerminalAt 704 8 8 checkedTerminal_704_8 checkedTerminal_712_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_720_8 : checkRange checkTerminalAt 720 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_728_8 : checkRange checkTerminalAt 728 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_720_16 : checkRange checkTerminalAt 720 16 = true := checkRange_join checkTerminalAt 720 8 8 checkedTerminal_720_8 checkedTerminal_728_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_704_32 : checkRange checkTerminalAt 704 32 = true := checkRange_join checkTerminalAt 704 16 16 checkedTerminal_704_16 checkedTerminal_720_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_736_8 : checkRange checkTerminalAt 736 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_744_8 : checkRange checkTerminalAt 744 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_736_16 : checkRange checkTerminalAt 736 16 = true := checkRange_join checkTerminalAt 736 8 8 checkedTerminal_736_8 checkedTerminal_744_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_752_8 : checkRange checkTerminalAt 752 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_760_8 : checkRange checkTerminalAt 760 8 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_752_16 : checkRange checkTerminalAt 752 16 = true := checkRange_join checkTerminalAt 752 8 8 checkedTerminal_752_8 checkedTerminal_760_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_736_32 : checkRange checkTerminalAt 736 32 = true := checkRange_join checkTerminalAt 736 16 16 checkedTerminal_736_16 checkedTerminal_752_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkedTerminal_704_64 : checkRange checkTerminalAt 704 64 = true := checkRange_join checkTerminalAt 704 32 32 checkedTerminal_704_32 checkedTerminal_736_32

end Paper2.Certificates.Q6.Coverage
