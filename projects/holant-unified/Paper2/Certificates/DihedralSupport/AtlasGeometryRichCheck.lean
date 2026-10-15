import Paper2.Certificates.DihedralSupport.AtlasGeometryCheck

namespace Paper2.Certificates.DihedralSupport.AtlasGeometryCheck
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem rich_lines_checked : checkRichLines = true := by decide +kernel

end Paper2.Certificates.DihedralSupport.AtlasGeometryCheck

