import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticCore
import Paper2.Certificates.DihedralSupport.AtlasVectors
import Paper2.Certificates.DihedralSupport.CyclotomicArithmeticField

/-! The exact Q(ω) atlas vectors interpret as the manuscript's original
V/E coefficient vectors at any root of Φ₃ in a characteristic-zero field. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic
open AtlasGeometry AtlasCounts AtlasVectors CyclotomicArithmetic
variable {K : Type*} [Field K] [CharZero K]

theorem singleVector_map (w : K) (hw : w^2+w+1=0)
    (p : Block) (r : Phase) :
    mapVector (embedField w hw) (singleVector omega p r)=singleVector w p r := by
  funext x
  by_cases hx : x.1=p
  · simp only [mapVector,singleVector,hx,ite_true,map_pow,embedField_omega]
  · simp only [mapVector,singleVector,hx,ite_false,map_zero]

theorem vector_map (w : K) (hw : w^2+w+1=0) (l : PointLabel) :
    mapVector (embedField w hw) (vector omega l)=vector w l := by
  cases l with
  | inl l => exact singleVector_map w hw l.1 l.2
  | inr l =>
    rcases l with ⟨p,r,t⟩
    have hp := congrFun (singleVector_map w hw p.1.1 r)
    have hq := congrFun (singleVector_map w hw p.1.2 t)
    funext x
    change embedField w hw (singleVector omega p.1.1 r x-singleVector omega p.1.2 t x)=_
    rw [map_sub]
    exact congrArg₂ (fun a b : K=>a-b) (hp x) (hq x)

theorem actual_minor2_eq (w : K) (hw : w^2+w+1=0)
    (a b : PointLabel) (x y : Coordinate) :
    minor2 (vector w a) (vector w b) x y=embedField w hw (minor2 (vector omega a) (vector omega b) x y) := by
  rw [←vector_map w hw a,←vector_map w hw b,map_minor2]

theorem actual_minor3_eq (w : K) (hw : w^2+w+1=0)
    (a b c : PointLabel) (x y z : Coordinate) :
    minor3 (vector w a) (vector w b) (vector w c) x y z=
      embedField w hw (minor3 (vector omega a) (vector omega b) (vector omega c) x y z) := by
  rw [←vector_map w hw a,←vector_map w hw b,←vector_map w hw c,map_minor3]

theorem actual_onLine_iff (w : K) (hw : w^2+w+1=0)
    (a b c : PointLabel) {x y : Coordinate}
    (h : minor2 (vector omega a) (vector omega b) x y≠0) :
    OnLine (vector w a) (vector w b) (vector w c) ↔
      OnLine (vector omega a) (vector omega b) (vector omega c) := by
  rw [←vector_map w hw a,←vector_map w hw b,←vector_map w hw c]
  exact onLine_map_iff (embedField w hw) h

theorem actual_proportional_iff (w : K) (hw : w^2+w+1=0)
    (a b : PointLabel) :
    Proportional (vector w a) (vector w b) ↔ Proportional (vector omega a) (vector omega b) := by
  rw [←vector_map w hw a,←vector_map w hw b]
  exact proportional_embedField_iff w hw _ _

end Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic

