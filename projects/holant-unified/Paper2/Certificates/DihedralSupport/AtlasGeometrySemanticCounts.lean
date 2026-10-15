import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticTables
import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticLines
import Paper2.Certificates.DihedralSupport.AtlasPencilsCardinality

/-! The displayed counts refer to actual four-port projective points and
actual two-dimensional subspaces over the full coefficient field. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic
open AtlasGeometry AtlasCounts AtlasParityFrame AtlasPencils
noncomputable section
variable {K : Type} [Field K] [CharZero K]

theorem table_projectivePoints_card (w : K) (hw : w^2+w+1=0) (epsilon : Bool) :
    (projectivePoints (table w epsilon)).card=66 :=
  projectivePoints_card _ (table_pair_independent w hw epsilon)

theorem table_mem_richLineSpace (w : K) (hw : w^2+w+1=0) (epsilon : Bool)
    (r : RichLabel) (l : PointLabel) :
    table w epsilon l∈richLineSpace (table w epsilon) r ↔ l∈richSet r := by
  rw [richLineSpace,←onLine_iff_mem_span]
  exact table_rich_line_membership w hw epsilon r l

theorem table_richLines_card (w : K) (hw : w^2+w+1=0) (epsilon : Bool) :
    (richLines (table w epsilon)).card=202 :=
  richLines_card _ (table_mem_richLineSpace w hw epsilon)

theorem table_richLines_complete (w : K) (hw : w^2+w+1=0) (epsilon : Bool)
    (L : Submodule K ((Fin 4→Bool)→K)) :
    L∈richLines (table w epsilon) ↔ RichLine (table w epsilon) L :=
  mem_richLines_iff _ (table_pair_independent w hw epsilon)
    (table_mem_richLineSpace w hw epsilon) (table_collinear_classify w hw epsilon) L

theorem table_rich_line_point_count (w : K) (hw : w^2+w+1=0) (epsilon : Bool)
    (L : Submodule K ((Fin 4→Bool)→K)) (hL : RichLine (table w epsilon) L) :
    (linePoints (table w epsilon) L).card=3 := by
  obtain ⟨r,rfl⟩ := richLines_complete _ (table_pair_independent w hw epsilon)
    (table_collinear_classify w hw epsilon) L hL
  exact rich_line_point_count _ (table_mem_richLineSpace w hw epsilon) r

end
end Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic

