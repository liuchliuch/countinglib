import Paper2.Certificates.DihedralSupport.AtlasGeometryCheck

namespace Paper2.Certificates.DihedralSupport.AtlasGeometryCheck
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem row_checked_1 : checkRow 1 = true := by decide +kernel
theorem row_checked_2 : checkRow 2 = true := by decide +kernel
theorem row_checked_3 : checkRow 3 = true := by decide +kernel
theorem row_checked_4 : checkRow 4 = true := by decide +kernel
theorem row_checked_5 : checkRow 5 = true := by decide +kernel
theorem row_checked_6 : checkRow 6 = true := by decide +kernel
theorem row_checked_7 : checkRow 7 = true := by decide +kernel
theorem row_checked_8 : checkRow 8 = true := by decide +kernel

end Paper2.Certificates.DihedralSupport.AtlasGeometryCheck
