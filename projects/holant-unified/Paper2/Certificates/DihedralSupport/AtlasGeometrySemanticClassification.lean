import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticVectors
import Paper2.Certificates.DihedralSupport.AtlasGeometryClassification

/-! The kernel-checked Q(ω) classification applies to the literal atlas in
every characteristic-zero field, including arbitrary complex coefficients. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic
open AtlasGeometry AtlasCounts AtlasVectors CyclotomicArithmetic
variable {K : Type*} [Field K] [CharZero K]

theorem actual_pair_independent (w : K) (hw : w^2+w+1=0)
    (l m : PointLabel) (hlm : l≠m) :
    ∃ a b : Coordinate, minor2 (vector w l) (vector w m) a b≠0 := by
  obtain ⟨a,b,hab⟩ := AtlasGeometryClassification.pair_independent l m hlm
  refine ⟨a,b,?_⟩
  rw [actual_minor2_eq w hw]
  exact fun hz => hab ((embedField_eq_zero_iff w hw _).mp hz)

theorem actual_zeroMinors_classify (w : K) (hw : w^2+w+1=0)
    (l m n : PointLabel) (hlm : l≠m) (hln : l≠n) (hmn : m≠n)
    (hz : ZeroMinors (vector w l) (vector w m) (vector w n)) :
    ∃ r : RichLabel, richSet r={l,m,n} := by
  apply AtlasGeometryClassification.classify l m n hlm hln hmn
  change ZeroMinors (vector omega l) (vector omega m) (vector omega n)
  intro a b c
  apply (embedField_eq_zero_iff w hw _).mp
  rw [←actual_minor3_eq w hw]
  exact hz a b c

theorem actual_collinear_classify (w : K) (hw : w^2+w+1=0)
    (l m n : PointLabel) (hlm : l≠m) (hln : l≠n) (hmn : m≠n)
    (h : OnLine (vector w l) (vector w m) (vector w n)) :
    ∃ r : RichLabel, richSet r={l,m,n} :=
  actual_zeroMinors_classify w hw l m n hlm hln hmn
    (fun a b c => minor3_eq_zero_of_onLine h a b c)

theorem actual_rich_onLine (w : K) (hw : w^2+w+1=0) (r : RichLabel) :
    OnLine (vector w (richPoints r 0)) (vector w (richPoints r 1))
      (vector w (richPoints r 2)) := by
  rw [←vector_map w hw,←vector_map w hw,←vector_map w hw]
  exact onLine_map (embedField w hw) (AtlasGeometryClassification.rich_onLine r)

theorem actual_rich_line_membership (w : K) (hw : w^2+w+1=0)
    (r : RichLabel) (l : PointLabel) :
    OnLine (vector w (richPoints r 0)) (vector w (richPoints r 1))
      (vector w l) ↔ l∈richSet r := by
  have h01 : richPoints r 0≠richPoints r 1 := fun hh => by
    have := richPoints_distinct r hh
    norm_num at this
  obtain ⟨a,b,hab⟩ := AtlasGeometryClassification.pair_independent _ _ h01
  rw [actual_onLine_iff w hw _ _ _ hab]
  exact AtlasGeometryClassification.rich_line_membership r l

end Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic

