import Paper2.Certificates.DihedralSupport.AtlasGeometryCheck

namespace Paper2.Certificates.DihedralSupport.AtlasGeometryCheck
open AtlasCounts AtlasVectors AtlasGeometry CyclotomicArithmetic AtlasGeometryData
set_option synthInstance.maxSize 10000
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- The certificate's coordinates are the literal defining V/E vectors. -/
theorem point_compatibility : ∀ i : Fin 66, ∀ x : Coordinate,
    point i.val x = vector omega (pointLabel i.val) x := by decide +kernel

theorem pointLabel_index : ∀ l ∈ pointList, pointLabel (pointList.idxOf l) = l :=
  by
    intro l h
    have hl := List.idxOf_lt_length_of_mem h
    unfold pointLabel
    rw [← List.getElem_eq_getD (single 0 0) (h := hl)]
    exact List.getElem_idxOf hl

theorem point_index_lt : ∀ l ∈ pointList, pointList.idxOf l < 66 := by
  intro l h
  simpa only [pointList_length] using List.idxOf_lt_length_of_mem h

theorem richLabel_index : ∀ r ∈ richList, richLabel (richList.idxOf r) = r :=
  by
    intro r h
    have hl := List.idxOf_lt_length_of_mem h
    unfold richLabel
    rw [← List.getElem_eq_getD (.inl 0) (h := hl)]
    exact List.getElem_idxOf hl

theorem rich_index_lt : ∀ r ∈ richList, richList.idxOf r < 202 := by
  intro r h
  simpa only [richList_length] using List.idxOf_lt_length_of_mem h

theorem richPoint_index : ∀ r ∈ richList, ∀ j : Fin 3,
    pointLabel (richIndex r j) = richPoints r j := by
  intro r _ j
  exact pointLabel_index _ (pointList_complete _)

theorem richPoint_index_lt : ∀ r ∈ richList, ∀ j : Fin 3,
    richIndex r j < 66 := by
  intro r _ j
  exact point_index_lt _ (pointList_complete _)

end Paper2.Certificates.DihedralSupport.AtlasGeometryCheck

