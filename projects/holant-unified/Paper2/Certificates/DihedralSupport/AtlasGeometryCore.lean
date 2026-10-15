import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Coordinate certificates for genuine projective lines.  The tests below
use exact field arithmetic; they neither approximate coefficients nor use a
finite-field specialization. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometry

variable {K : Type*} [Field K] {I : Type*}

def minor2 (u v : I → K) (a b : I) : K := u a * v b - u b * v a

def minor3 (u v w : I → K) (a b c : I) : K :=
  u a * (v b * w c - v c * w b) -
    u b * (v a * w c - v c * w a) + u c * (v a * w b - v b * w a)

/-- Membership in the actual two-dimensional linear span. -/
def OnLine (u v w : I → K) : Prop := ∃ α β : K, α • u + β • v = w

def ZeroMinors (u v w : I → K) : Prop := ∀ a b c, minor3 u v w a b c = 0

theorem zeroMinors_swap_left {u v w : I → K} (h : ZeroMinors u v w) :
    ZeroMinors v u w := by
  intro a b c
  have hh := h a b c
  dsimp [minor3] at *
  linear_combination -hh

theorem zeroMinors_swap_right {u v w : I → K} (h : ZeroMinors u v w) :
    ZeroMinors u w v := by
  intro a b c
  have hh := h a b c
  dsimp [minor3] at *
  linear_combination -hh

theorem onLine_iff_mem_span (u v w : I → K) :
    OnLine u v w ↔ w ∈ Submodule.span K ({u,v} : Set (I → K)) := by
  exact Submodule.mem_span_pair.symm

theorem minor3_eq_zero_of_onLine {u v w : I → K} (h : OnLine u v w)
    (a b c : I) : minor3 u v w a b c = 0 := by
  obtain ⟨α,β,rfl⟩ := h
  simp only [minor3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem zeroMinors_of_three_onLine {u v x y z : I → K}
    (hx : OnLine u v x) (hy : OnLine u v y) (hz : OnLine u v z) :
    ZeroMinors x y z := by
  obtain ⟨a,b,rfl⟩ := hx
  obtain ⟨c,d,rfl⟩ := hy
  obtain ⟨e,f,rfl⟩ := hz
  intro i j k
  simp only [minor3,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem not_onLine_of_minor3_ne_zero {u v w : I → K} {a b c : I}
    (h : minor3 u v w a b c ≠ 0) : ¬ OnLine u v w := by
  exact fun hline => h (minor3_eq_zero_of_onLine hline a b c)

/-- A single nonzero two-by-two minor provides the exact linear coefficients.
Only the remaining three-by-three minors need be checked. -/
theorem onLine_of_minor3_zero {u v w : I → K} {a b : I}
    (h : minor2 u v a b ≠ 0) (hz : ∀ c, minor3 u v w a b c = 0) :
    OnLine u v w := by
  refine ⟨(w a * v b - w b * v a) / minor2 u v a b,
    (u a * w b - u b * w a) / minor2 u v a b, ?_⟩
  funext c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hc := hz c
  field_simp [h]
  dsimp [minor2, minor3] at *
  linear_combination -hc

theorem onLine_iff_zeroMinors {u v w : I → K} {a b : I}
    (h : minor2 u v a b ≠ 0) : OnLine u v w ↔ ZeroMinors u v w := by
  exact ⟨fun hz a b c => minor3_eq_zero_of_onLine hz a b c,
    fun hz => onLine_of_minor3_zero h (hz a b)⟩

theorem nonzero_left_of_minor2 {u v : I → K} {a b : I}
    (h : minor2 u v a b ≠ 0) : u ≠ 0 := by
  rintro rfl
  simp [minor2] at h

theorem not_proportional_of_minor2 {u v : I → K} {a b : I}
    (h : minor2 u v a b ≠ 0) : ¬ ∃ α : K, α • u = v := by
  rintro ⟨α,rfl⟩
  apply h
  simp only [minor2, Pi.smul_apply, smul_eq_mul]
  ring

end Paper2.Certificates.DihedralSupport.AtlasGeometry
