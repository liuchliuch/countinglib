module
public import Paper2.Certificates.DihedralSupport.Data

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1008 : rowCheck 1008 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1009 : rowCheck 1009 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1010 : rowCheck 1010 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1011 : rowCheck 1011 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1012 : rowCheck 1012 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1013 : rowCheck 1013 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1014 : rowCheck 1014 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1015 : rowCheck 1015 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1016 : rowCheck 1016 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1017 : rowCheck 1017 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1018 : rowCheck 1018 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1019 : rowCheck 1019 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1020 : rowCheck 1020 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1021 : rowCheck 1021 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1022 : rowCheck 1022 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_1023 : rowCheck 1023 = true := by decide +kernel

theorem range_checked_63 : checkRange rowCheck 1008 16 = true := by
  simp only [checkRange, Nat.reduceAdd, row_checked_1008,row_checked_1009,row_checked_1010,row_checked_1011,row_checked_1012,row_checked_1013,row_checked_1014,row_checked_1015,row_checked_1016,row_checked_1017,row_checked_1018,row_checked_1019,row_checked_1020,row_checked_1021,row_checked_1022,row_checked_1023, Bool.and_self]

end Paper2.Certificates.DihedralSupport
