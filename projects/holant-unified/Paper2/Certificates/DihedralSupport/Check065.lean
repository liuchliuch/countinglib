module
public import Paper2.Certificates.DihedralSupport.Data

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1040 : rowCheck 1040 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1041 : rowCheck 1041 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1042 : rowCheck 1042 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1043 : rowCheck 1043 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1044 : rowCheck 1044 = true := by decide +kernel

theorem range_checked_65 : checkRange rowCheck 1040 5 = true := by
  simp only [checkRange, Nat.reduceAdd, row_checked_1040,row_checked_1041,row_checked_1042,row_checked_1043,row_checked_1044, Bool.and_self]

end Paper2.Certificates.DihedralSupport
