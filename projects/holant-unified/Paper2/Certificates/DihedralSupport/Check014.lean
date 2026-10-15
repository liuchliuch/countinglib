module
public import Paper2.Certificates.DihedralSupport.Data

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_224 : rowCheck 224 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_225 : rowCheck 225 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_226 : rowCheck 226 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_227 : rowCheck 227 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_228 : rowCheck 228 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_229 : rowCheck 229 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_230 : rowCheck 230 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_231 : rowCheck 231 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_232 : rowCheck 232 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_233 : rowCheck 233 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_234 : rowCheck 234 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_235 : rowCheck 235 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_236 : rowCheck 236 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_237 : rowCheck 237 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_238 : rowCheck 238 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_239 : rowCheck 239 = true := by decide +kernel

theorem range_checked_14 : checkRange rowCheck 224 16 = true := by
  simp only [checkRange, Nat.reduceAdd, row_checked_224,row_checked_225,row_checked_226,row_checked_227,row_checked_228,row_checked_229,row_checked_230,row_checked_231,row_checked_232,row_checked_233,row_checked_234,row_checked_235,row_checked_236,row_checked_237,row_checked_238,row_checked_239, Bool.and_self]

end Paper2.Certificates.DihedralSupport
