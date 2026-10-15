module
public import Paper2.Certificates.DihedralSupport.Data

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_416 : rowCheck 416 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_417 : rowCheck 417 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_418 : rowCheck 418 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_419 : rowCheck 419 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_420 : rowCheck 420 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_421 : rowCheck 421 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_422 : rowCheck 422 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_423 : rowCheck 423 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_424 : rowCheck 424 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_425 : rowCheck 425 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_426 : rowCheck 426 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_427 : rowCheck 427 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_428 : rowCheck 428 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_429 : rowCheck 429 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_430 : rowCheck 430 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_431 : rowCheck 431 = true := by decide +kernel

theorem range_checked_26 : checkRange rowCheck 416 16 = true := by
  simp only [checkRange, Nat.reduceAdd, row_checked_416,row_checked_417,row_checked_418,row_checked_419,row_checked_420,row_checked_421,row_checked_422,row_checked_423,row_checked_424,row_checked_425,row_checked_426,row_checked_427,row_checked_428,row_checked_429,row_checked_430,row_checked_431, Bool.and_self]

end Paper2.Certificates.DihedralSupport
