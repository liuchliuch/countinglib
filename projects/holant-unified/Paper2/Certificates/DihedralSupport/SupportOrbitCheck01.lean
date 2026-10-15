module
public import Paper2.Certificates.DihedralSupport.SupportOrbitData
@[expose] public section
namespace Paper2.Certificates.DihedralSupport.SupportOrbit
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem check_01 : checkRange validAt 80 80 = true := by decide +kernel
end Paper2.Certificates.DihedralSupport.SupportOrbit
