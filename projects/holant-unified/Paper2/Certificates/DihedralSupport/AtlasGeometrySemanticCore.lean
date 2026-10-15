import Paper2.Certificates.DihedralSupport.AtlasGeometryCore
import Paper2.Certificates.DihedralSupport.CyclotomicArithmetic

/-! Exact scalar extension for the finite atlas. Every minor is interpreted
by the actual field embedding. Conversely, a line relation with arbitrary
extension-field coefficients descends through the proved minor criterion. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic
open AtlasGeometry CyclotomicArithmetic

variable {K L I : Type*} [Field K] [Field L]

def mapVector (f : K→+*L) (u : I→K) : I→L := fun i=>f (u i)

theorem mapVector_injective (f : K→+*L) : Function.Injective (mapVector (I:=I) f) := by
  intro u v h
  funext i
  apply f.injective
  exact congrFun h i

theorem map_minor2 (f : K→+*L) (u v : I→K) (a b : I) :
    minor2 (mapVector f u) (mapVector f v) a b=f (minor2 u v a b) := by
  simp only [minor2,mapVector,map_sub,map_mul]

theorem map_minor3 (f : K→+*L) (u v t : I→K) (a b c : I) :
    minor3 (mapVector f u) (mapVector f v) (mapVector f t) a b c=
      f (minor3 u v t a b c) := by
  simp only [minor3,mapVector,map_add,map_sub,map_mul]

theorem minor2_map_eq_zero_iff (f : K→+*L) (u v : I→K) (a b : I) :
    minor2 (mapVector f u) (mapVector f v) a b=0 ↔ minor2 u v a b=0 := by
  rw [map_minor2]
  exact map_eq_zero_iff f f.injective

theorem minor3_map_eq_zero_iff (f : K→+*L) (u v t : I→K) (a b c : I) :
    minor3 (mapVector f u) (mapVector f v) (mapVector f t) a b c=0 ↔
      minor3 u v t a b c=0 := by
  rw [map_minor3]
  exact map_eq_zero_iff f f.injective

theorem onLine_map (f : K→+*L) {u v t : I→K} (h : OnLine u v t) :
    OnLine (mapVector f u) (mapVector f v) (mapVector f t) := by
  obtain ⟨a,b,rfl⟩ := h
  refine ⟨f a,f b,?_⟩
  funext i
  simp only [mapVector,Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul]

/-- No assumption is made that the extension-field coefficients of a line
relation belong to the smaller field. The nonzero pivot and exact minors
recover actual coefficients in the smaller field. -/
theorem onLine_map_iff (f : K→+*L) {u v t : I→K} {a b : I}
    (h : minor2 u v a b≠0) :
    OnLine (mapVector f u) (mapVector f v) (mapVector f t) ↔ OnLine u v t := by
  constructor
  · intro hz
    apply onLine_of_minor3_zero h
    intro c
    apply (minor3_map_eq_zero_iff f u v t a b c).mp
    exact minor3_eq_zero_of_onLine hz a b c
  · exact onLine_map f

theorem span_map_iff (f : K→+*L) {u v t : I→K} {a b : I}
    (h : minor2 u v a b≠0) :
    mapVector f t ∈ Submodule.span L ({mapVector f u,mapVector f v} : Set (I→L)) ↔
      t ∈ Submodule.span K ({u,v} : Set (I→K)) := by
  rw [←onLine_iff_mem_span,←onLine_iff_mem_span]
  exact onLine_map_iff f h

end Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic

