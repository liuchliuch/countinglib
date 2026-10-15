module
public import Paper2.Certificates.DihedralSupport.Data

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_592 : rowCheck 592 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_593 : rowCheck 593 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_594 : rowCheck 594 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_595 : rowCheck 595 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_596 : rowCheck 596 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_597 : rowCheck 597 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_598 : rowCheck 598 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_599 : rowCheck 599 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_600 : rowCheck 600 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_601 : rowCheck 601 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_602 : rowCheck 602 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_603 : rowCheck 603 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_604 : rowCheck 604 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_605 : rowCheck 605 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_606 : rowCheck 606 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_607 : rowCheck 607 = true := by decide +kernel

theorem range_checked_37 : checkRange rowCheck 592 16 = true := by
  simp only [checkRange, Nat.reduceAdd, row_checked_592,row_checked_593,row_checked_594,row_checked_595,row_checked_596,row_checked_597,row_checked_598,row_checked_599,row_checked_600,row_checked_601,row_checked_602,row_checked_603,row_checked_604,row_checked_605,row_checked_606,row_checked_607, Bool.and_self]

end Paper2.Certificates.DihedralSupport
