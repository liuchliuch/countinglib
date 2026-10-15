import Paper2.Certificates.DihedralSupport.AtlasPencils
import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticLinear

/-! Coordinate minors and the source's literal linear independence condition
are equivalent. No finite dimension, normalized representative, or nonzero
entry witness is supplied by the caller. -/
namespace Paper2.Certificates.DihedralSupport.AtlasPencils
open AtlasGeometry AtlasGeometrySemantic

variable {K I : Type*} [Field K]

theorem pairIndependent_iff_minor (u v : I → K) :
    LinearIndependent K ![u,v] ↔ ∃ a b : I, minor2 u v a b ≠ 0 := by
  classical
  constructor
  · intro h
    have hu : u ≠ 0 := by simpa using h.ne_zero (0 : Fin 2)
    obtain ⟨a,ha⟩ : ∃ a, u a ≠ 0 := by
      by_contra hn
      apply hu
      funext a
      by_contra ha
      exact hn ⟨a,ha⟩
    by_contra hn
    have hz : ∀ a b, minor2 u v a b = 0 := by
      intro a b
      by_contra hab
      exact hn ⟨a,b,hab⟩
    have hp : (v a / u a) • u = v := by
      funext b
      have hb := hz a b
      simp only [Pi.smul_apply,smul_eq_mul]
      field_simp [ha]
      dsimp [minor2] at hb
      linear_combination -hb
    exact ((LinearIndependent.pair_iff' hu).mp h) _ hp
  · rintro ⟨a,b,hab⟩
    exact independent_of_minor2 hab

theorem nonconstant_iff_linearIndependent (P : Pencil K I) :
    Nonconstant P ↔ LinearIndependent K ![P.A,P.B] :=
  (pairIndependent_iff_minor P.A P.B).symm

end Paper2.Certificates.DihedralSupport.AtlasPencils

