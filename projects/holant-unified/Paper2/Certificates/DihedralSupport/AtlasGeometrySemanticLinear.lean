import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticCore
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fin.VecNotation

/-! Actual projective line dimensions and uniqueness. A nonzero coordinate
minor proves independence in the full coefficient field; two such points in
any two-dimensional subspace determine that entire subspace. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic
open AtlasGeometry

variable {K I : Type*} [Field K]

theorem independent_of_minor2 {u v : I→K} {a b : I}
    (h : minor2 u v a b≠0) : LinearIndependent K ![u,v] := by
  apply (LinearIndependent.pair_iff' (nonzero_left_of_minor2 h)).mpr
  intro c hc
  exact not_proportional_of_minor2 h ⟨c,hc⟩

theorem span_pair_finrank {u v : I→K} {a b : I}
    (h : minor2 u v a b≠0) : Module.finrank K (Submodule.span K ({u,v} : Set (I→K)))=2 := by
  rw [←Matrix.range_cons_cons_empty u v ![]]
  simpa using finrank_span_eq_card (independent_of_minor2 h)

theorem two_dimensional_line_eq_span {u v : I→K} {a b : I}
    (h : minor2 u v a b≠0) (L : Submodule K (I→K))
    (hdim : Module.finrank K L=2) (hu : u∈L) (hv : v∈L) :
    L=Submodule.span K ({u,v} : Set (I→K)) := by
  have hle : Submodule.span K ({u,v} : Set (I→K))≤L := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact hu
    · have he : x=v := Set.mem_singleton_iff.mp hx
      exact he ▸ hv
  letI : Module.Finite K L := Module.finite_of_finrank_eq_succ hdim
  exact (Submodule.eq_of_le_of_finrank_eq hle ((span_pair_finrank h).trans hdim.symm)).symm

end Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic

