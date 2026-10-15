module
public import Paper2.Certificates.DihedralSupport.Data

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_992 : rowCheck 992 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_993 : rowCheck 993 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_994 : rowCheck 994 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_995 : rowCheck 995 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_996 : rowCheck 996 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_997 : rowCheck 997 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_998 : rowCheck 998 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_999 : rowCheck 999 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1000 : rowCheck 1000 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1001 : rowCheck 1001 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1002 : rowCheck 1002 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1003 : rowCheck 1003 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1004 : rowCheck 1004 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1005 : rowCheck 1005 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1006 : rowCheck 1006 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1007 : rowCheck 1007 = true := by decide +kernel

theorem range_checked_62 : checkRange rowCheck 992 16 = true := by
  simp only [checkRange, Nat.reduceAdd, row_checked_992,row_checked_993,row_checked_994,row_checked_995,row_checked_996,row_checked_997,row_checked_998,row_checked_999,row_checked_1000,row_checked_1001,row_checked_1002,row_checked_1003,row_checked_1004,row_checked_1005,row_checked_1006,row_checked_1007, Bool.and_self]

end Paper2.Certificates.DihedralSupport
