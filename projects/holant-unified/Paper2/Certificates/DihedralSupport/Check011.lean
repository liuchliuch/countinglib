module
public import Paper2.Certificates.DihedralSupport.Data

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_176 : rowCheck 176 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_177 : rowCheck 177 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_178 : rowCheck 178 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_179 : rowCheck 179 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_180 : rowCheck 180 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_181 : rowCheck 181 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_182 : rowCheck 182 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_183 : rowCheck 183 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_184 : rowCheck 184 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_185 : rowCheck 185 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_186 : rowCheck 186 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_187 : rowCheck 187 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_188 : rowCheck 188 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_189 : rowCheck 189 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_190 : rowCheck 190 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_checked_191 : rowCheck 191 = true := by decide +kernel

theorem range_checked_11 : checkRange rowCheck 176 16 = true := by
  simp only [checkRange, Nat.reduceAdd, row_checked_176,row_checked_177,row_checked_178,row_checked_179,row_checked_180,row_checked_181,row_checked_182,row_checked_183,row_checked_184,row_checked_185,row_checked_186,row_checked_187,row_checked_188,row_checked_189,row_checked_190,row_checked_191, Bool.and_self]

end Paper2.Certificates.DihedralSupport
