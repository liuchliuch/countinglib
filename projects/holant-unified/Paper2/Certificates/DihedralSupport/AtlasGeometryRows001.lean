import Paper2.Certificates.DihedralSupport.AtlasGeometryCheck

namespace Paper2.Certificates.DihedralSupport.AtlasGeometryCheck
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem row_checked_9 : checkRow 9 = true := by decide +kernel
theorem row_checked_10 : checkRow 10 = true := by decide +kernel
theorem row_checked_11 : checkRow 11 = true := by decide +kernel
theorem row_checked_12 : checkRow 12 = true := by decide +kernel
theorem row_checked_13 : checkRow 13 = true := by decide +kernel
theorem row_checked_14 : checkRow 14 = true := by decide +kernel
theorem row_checked_15 : checkRow 15 = true := by decide +kernel
theorem row_checked_16 : checkRow 16 = true := by decide +kernel

end Paper2.Certificates.DihedralSupport.AtlasGeometryCheck
