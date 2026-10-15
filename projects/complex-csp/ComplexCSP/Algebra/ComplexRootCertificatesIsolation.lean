import ComplexCSP.Algebra.ComplexRootCertificatesInput
import Mathlib.Algebra.Polynomial.Roots

/-!
# Rational isolating rectangles without a simple-root assumption

Multiplicity is irrelevant: a nonzero polynomial has finitely many distinct
complex roots. Every one of those roots has a rational rectangle whose closed
boundary contains no other root.
-/

namespace ComplexCSP.ComplexRootCertificates

open Polynomial
open scoped Topology

/-- Closed-rectangle membership, useful for exclusion of all other roots even
on the rectangle's boundary. -/
def Rectangle.ClosedContains (box : Rectangle) (z : ℂ) : Prop :=
  (box.reLo : ℝ) ≤ z.re ∧ z.re ≤ (box.reHi : ℝ) ∧
  (box.imLo : ℝ) ≤ z.im ∧ z.im ≤ (box.imHi : ℝ)

theorem Rectangle.Contains.closed {box : Rectangle} {z : ℂ} (h : box.Contains z) :
    box.ClosedContains z := ⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

/-- A rational rectangle can be placed inside any complex neighborhood, while
strictly containing its specified center. -/
theorem exists_rectangle_within_disk (α : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ box : Rectangle, box.Contains α ∧
      ∀ z, box.ClosedContains z → ‖z-α‖ < ε := by
  obtain ⟨rl,hrl₁,hrl₂⟩ := exists_rat_btwn (show α.re-ε/4 < α.re by linarith)
  obtain ⟨rh,hrh₁,hrh₂⟩ := exists_rat_btwn (show α.re < α.re+ε/4 by linarith)
  obtain ⟨il,hil₁,hil₂⟩ := exists_rat_btwn (show α.im-ε/4 < α.im by linarith)
  obtain ⟨ih,hih₁,hih₂⟩ := exists_rat_btwn (show α.im < α.im+ε/4 by linarith)
  let box : Rectangle := ⟨rl,rh,il,ih⟩
  refine ⟨box, ⟨hrl₂,hrh₁,hil₂,hih₁⟩, ?_⟩
  intro z hz
  have hre : |z.re-α.re| < ε/4 := abs_lt.mpr ⟨by have := hz.1; change (rl:ℝ) ≤ z.re at this; linarith,
    by have := hz.2.1; change z.re ≤ (rh:ℝ) at this; linarith⟩
  have him : |z.im-α.im| < ε/4 := abs_lt.mpr ⟨by have := hz.2.2.1; change (il:ℝ) ≤ z.im at this; linarith,
    by have := hz.2.2.2; change z.im ≤ (ih:ℝ) at this; linarith⟩
  apply lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _)
  simp only [Complex.sub_re, Complex.sub_im]
  linarith

/-- Every root of a nonzero polynomial admits a rational isolating rectangle.
The root is allowed to have arbitrary multiplicity. -/
theorem exists_isolating_rectangle (p : Polynomial ℂ) (hp : p ≠ 0)
    (α : ℂ) (_hα : p.eval α = 0) :
    ∃ box : Rectangle, box.Contains α ∧
      ∀ z, box.ClosedContains z → p.eval z = 0 → z = α := by
  let S : Set ℂ := {z | p.IsRoot z} \ {α}
  have hS : S.Finite := (Polynomial.finite_setOf_isRoot hp).diff
  have hαS : α ∈ Sᶜ := by simp [S]
  have hopen : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hαS)
  obtain ⟨box,hbox,hnear⟩ := exists_rectangle_within_disk α hε
  refine ⟨box,hbox,?_⟩
  intro z hz hzroot
  have hnot := hball (show z ∈ Metric.ball α ε from by
    simpa only [Metric.mem_ball, dist_eq_norm] using hnear z hz)
  by_contra hne
  exact hnot ⟨hzroot,hne⟩

/-- Open-rectangle uniqueness follows from the stronger closed-boundary result. -/
theorem exists_unique_root_rectangle (p : Polynomial ℂ) (hp : p ≠ 0)
    (α : ℂ) (hα : p.eval α = 0) :
    ∃ box : Rectangle, box.Contains α ∧ ∃! z, box.Contains z ∧ p.eval z = 0 := by
  obtain ⟨box,hbox,hunique⟩ := exists_isolating_rectangle p hp α hα
  exact ⟨box,hbox,α,⟨hbox,hα⟩,fun z hz ↦ hunique z hz.1.closed hz.2⟩

end ComplexCSP.ComplexRootCertificates
