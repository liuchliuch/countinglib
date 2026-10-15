import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticCounts
import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticCategories
import Paper2.Certificates.DihedralSupport.AtlasPencilsCompleteness
import Paper2.Certificates.DihedralSupport.CyclotomicComplex

/-! Appendix A.1(i), for the actual signatures and actual geometric objects
in the full ambient coefficient field. All counts and exhaustivity follow
from the exact atlas construction and its kernel-checked minor certificates. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic
open AtlasGeometry AtlasCounts AtlasParityFrame AtlasPencils
noncomputable section
variable {K : Type} [Field K] [CharZero K]

theorem table_tripleExhaustive (w : K) (hw : w^2+w+1=0) (epsilon : Bool) :
    TripleExhaustive (table w epsilon) := by
  intro p hp hline
  have h01 : p 0≠p 1 := fun hh => by
    have := hp hh; norm_num at this
  have h02 : p 0≠p 2 := fun hh => by
    have := hp hh; norm_num at this
  have h12 : p 1≠p 2 := fun hh => by
    have := hp hh; norm_num at this
  obtain ⟨r,hr⟩ := table_collinear_classify w hw epsilon _ _ _ h01 h02 h12 hline
  refine ⟨r,?_⟩
  rw [hr]
  ext l
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨j,rfl⟩
    fin_cases j <;> simp
  · intro h
    rcases h with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

/-- The complete source geometry packet, including the entire set of actual
admissible pencils modulo a common nonzero scalar. -/
structure AtlasStatement (w : K) (epsilon : Bool) : Prop where
  point_count : (projectivePoints (table w epsilon)).card=66
  rich_line_count : (richLines (table w epsilon)).card=202
  rich_line_complete : ∀ L : Submodule K ((Fin 4→Bool)→K),
    L∈richLines (table w epsilon) ↔ RichLine (table w epsilon) L
  line_point_count : ∀ L : Submodule K ((Fin 4→Bool)→K),
    RichLine (table w epsilon) L → (linePoints (table w epsilon) L).card=3
  one_block_line_count : (oneBlockLines (table w epsilon)).card=4
  ruling_line_count : (rulingLines (table w epsilon)).card=36
  secant_line_count : (secantLines (table w epsilon)).card=54
  triangle_line_count : (triangleLines (table w epsilon)).card=108
  line_categories : richLines (table w epsilon)=
    oneBlockLines (table w epsilon) ∪ rulingLines (table w epsilon) ∪
      secantLines (table w epsilon) ∪ triangleLines (table w epsilon)
  pencil_count : Nat.card (admissibleClasses (table w epsilon)
    (fun r : Fin 3 => w^r.val))=1212

theorem source_A_1_i (w : K) (hw : w^2+w+1=0) (epsilon : Bool) :
    AtlasStatement w epsilon := by
  have hinc := table_mem_richLineSpace w hw epsilon
  refine ⟨table_projectivePoints_card w hw epsilon,table_richLines_card w hw epsilon,
    table_richLines_complete w hw epsilon,table_rich_line_point_count w hw epsilon,
    oneBlockLines_card _ hinc,rulingLines_card _ hinc,secantLines_card _ hinc,
    triangleLines_card _ hinc,richLines_categories _,?_⟩
  exact admissibleClasses_card _ _ (table_pair_independent w hw epsilon)
    (CyclotomicComplex.phase_injective w hw) (table_rich_onLine w hw epsilon)
    (table_tripleExhaustive w hw epsilon)

end
end Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic

