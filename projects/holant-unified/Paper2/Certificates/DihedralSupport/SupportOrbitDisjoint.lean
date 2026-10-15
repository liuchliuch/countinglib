module
public import Paper2.Certificates.DihedralSupport.SupportOrbit
public import Paper2.Certificates.DihedralSupport.EvenPartitionCosets

@[expose] public section
namespace Paper2.Certificates.DihedralSupport.SupportOrbit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The two literal generated families have no common support. -/
theorem orbit_affine_disjoint : Disjoint orbitMasks affineMasks := by
  rw [orbitMasks_eq_data]
  decide +kernel

theorem zero_not_mem : 0 ∉ orbitMasks := by
  intro h
  exact orbit_nonzero h rfl

end Paper2.Certificates.DihedralSupport.SupportOrbit
