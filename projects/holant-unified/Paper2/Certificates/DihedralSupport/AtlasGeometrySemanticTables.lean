import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticClassification
import Paper2.Certificates.DihedralSupport.AtlasParityFrameGeometry

/-! Literal four-port signatures in either parity frame inherit the exact
point and rich-line classification over arbitrary characteristic-zero fields. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic
open AtlasGeometry AtlasCounts AtlasVectors AtlasParityFrame
variable {K : Type} [Field K] [CharZero K]

theorem table_pair_independent (w : K) (hw : w^2+w+1=0) (epsilon : Bool)
    (l m : PointLabel) (hlm : l≠m) :
    ∃ a b : Fin 4→Bool, minor2 (table w epsilon l) (table w epsilon m) a b≠0 := by
  obtain ⟨a,b,hab⟩ := actual_pair_independent w hw l m hlm
  exact ⟨word epsilon a,word epsilon b,by
    simpa only [minor2,table_word] using hab⟩

theorem table_zeroMinors_classify (w : K) (hw : w^2+w+1=0) (epsilon : Bool)
    (l m n : PointLabel) (hlm : l≠m) (hln : l≠n) (hmn : m≠n)
    (hz : ZeroMinors (table w epsilon l) (table w epsilon m) (table w epsilon n)) :
    ∃ r : RichLabel, richSet r={l,m,n} := by
  apply actual_zeroMinors_classify w hw l m n hlm hln hmn
  exact (zeroMinors_extend_iff epsilon _ _ _).mp hz

theorem table_collinear_classify (w : K) (hw : w^2+w+1=0) (epsilon : Bool)
    (l m n : PointLabel) (hlm : l≠m) (hln : l≠n) (hmn : m≠n)
    (h : OnLine (table w epsilon l) (table w epsilon m) (table w epsilon n)) :
    ∃ r : RichLabel, richSet r={l,m,n} := by
  exact actual_collinear_classify w hw l m n hlm hln hmn
    ((onLine_table_iff w epsilon l m n).mp h)

theorem table_rich_onLine (w : K) (hw : w^2+w+1=0) (epsilon : Bool)
    (r : RichLabel) :
    OnLine (table w epsilon (richPoints r 0)) (table w epsilon (richPoints r 1))
      (table w epsilon (richPoints r 2)) :=
  (onLine_table_iff w epsilon _ _ _).mpr (actual_rich_onLine w hw r)

theorem table_rich_line_membership (w : K) (hw : w^2+w+1=0) (epsilon : Bool)
    (r : RichLabel) (l : PointLabel) :
    OnLine (table w epsilon (richPoints r 0)) (table w epsilon (richPoints r 1))
      (table w epsilon l) ↔ l∈richSet r := by
  rw [onLine_table_iff]
  exact actual_rich_line_membership w hw r l

end Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic

