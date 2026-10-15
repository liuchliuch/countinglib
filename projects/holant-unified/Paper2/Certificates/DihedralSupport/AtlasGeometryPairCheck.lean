import Paper2.Certificates.DihedralSupport.AtlasGeometryCheck
import Paper2.Certificates.DihedralSupport.AtlasGeometryPairData

namespace Paper2.Certificates.DihedralSupport.AtlasGeometryCheck
open AtlasGeometry AtlasGeometryPairData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def pairCode (i j : ℕ) : ℕ := (pairCodes.getD i []).getD j 0

def pairCertificate : Bool := (List.range 66).all fun i => (List.range 66).all fun j =>
  if i < j then decide (minor2 (point i) (point j)
    (coordinate ((pairCode i j / 8)%8)) (coordinate (pairCode i j % 8)) ≠ 0)
  else true

theorem pair_certificate_checked : pairCertificate = true := by decide +kernel

theorem pairs_checked : checkPairs = true := by
  apply List.all_eq_true.mpr
  intro i hi
  apply List.all_eq_true.mpr
  intro j hj
  split_ifs with hij
  · have hr := List.all_eq_true.mp
      (List.all_eq_true.mp pair_certificate_checked i hi) j hj
    simp only [ite_eq_left hij] at hr
    have hc : minor2 (point i) (point j)
        (coordinate ((pairCode i j / 8)%8)) (coordinate (pairCode i j%8)) ≠ 0 :=
      of_decide_eq_true hr
    apply List.any_eq_true.mpr
    refine ⟨(pairCode i j / 8)%8,List.mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩
    apply List.any_eq_true.mpr
    refine ⟨pairCode i j%8,List.mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩
    exact decide_eq_true hc
  · rfl

end Paper2.Certificates.DihedralSupport.AtlasGeometryCheck

