module
public import Paper2.Certificates.DihedralSupport.Data

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1024 : rowCheck 1024 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1025 : rowCheck 1025 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1026 : rowCheck 1026 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1027 : rowCheck 1027 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1028 : rowCheck 1028 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1029 : rowCheck 1029 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1030 : rowCheck 1030 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1031 : rowCheck 1031 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1032 : rowCheck 1032 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1033 : rowCheck 1033 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1034 : rowCheck 1034 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1035 : rowCheck 1035 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1036 : rowCheck 1036 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1037 : rowCheck 1037 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1038 : rowCheck 1038 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1039 : rowCheck 1039 = true := by decide +kernel

theorem range_checked_64 : checkRange rowCheck 1024 16 = true := by
  simp only [checkRange, Nat.reduceAdd, row_checked_1024,row_checked_1025,row_checked_1026,row_checked_1027,row_checked_1028,row_checked_1029,row_checked_1030,row_checked_1031,row_checked_1032,row_checked_1033,row_checked_1034,row_checked_1035,row_checked_1036,row_checked_1037,row_checked_1038,row_checked_1039, Bool.and_self]

end Paper2.Certificates.DihedralSupport
