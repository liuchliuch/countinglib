module
public import Paper2.Certificates.DihedralSupport.Data

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_96 : rowCheck 96 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_97 : rowCheck 97 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_98 : rowCheck 98 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_99 : rowCheck 99 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_100 : rowCheck 100 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_101 : rowCheck 101 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_102 : rowCheck 102 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_103 : rowCheck 103 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_104 : rowCheck 104 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_105 : rowCheck 105 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_106 : rowCheck 106 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_107 : rowCheck 107 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_108 : rowCheck 108 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_109 : rowCheck 109 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_110 : rowCheck 110 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_111 : rowCheck 111 = true := by decide +kernel

theorem range_checked_6 : checkRange rowCheck 96 16 = true := by
  simp only [checkRange, Nat.reduceAdd, row_checked_96,row_checked_97,row_checked_98,row_checked_99,row_checked_100,row_checked_101,row_checked_102,row_checked_103,row_checked_104,row_checked_105,row_checked_106,row_checked_107,row_checked_108,row_checked_109,row_checked_110,row_checked_111, Bool.and_self]

end Paper2.Certificates.DihedralSupport
