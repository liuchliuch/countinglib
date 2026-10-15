import Holant.ReedMuller.AffinePatching.ReconstructionSupport
import Paper2.DegreeCSP.BooleanGeneratedAffineSupport
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Select actual original coordinates on an affine support. Projection onto
these coordinates is a bijection, so marginalizing the other coordinates has
exactly one nonzero summand at every retained word. No affine substitution
gadget or Hadamard signature is assumed. -/
namespace Paper2.DegreeCSP.AffineSupportCoordinates
open Tractable Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem subspace_coordinates {K : Type} [Field K] {n : ℕ}
    (D : Submodule K (Fin n → K)) :
    ∃ (r : ℕ) (q : Fin r → Fin n), Function.Injective q ∧
      Function.Bijective (fun v : D => fun j => v.val (q j)) := by
  classical
  let coord : Fin n → Module.Dual K D :=
    fun i => (LinearMap.proj i).comp D.subtype
  have hspan : Submodule.span K (Set.range coord) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro v hv
    have hi : ∃ i, v.val i ≠ 0 := by
      by_contra hn
      apply hv
      apply Subtype.ext
      funext i
      exact not_not.mp (not_exists.mp hn i)
    obtain ⟨i,hi⟩ := hi
    exact ⟨coord i,⟨i,rfl⟩,hi⟩
  let I : Type := (linearIndepOn_empty K id).extend (Set.empty_subset (Set.range coord))
  let B : Basis I K (Module.Dual K D) := Basis.ofSpan hspan.ge
  letI := FiniteDimensional.fintypeBasisIndex B
  have hmem : ∀ i, B i ∈ Set.range coord := by
    intro i
    exact Basis.ofSpan_subset hspan.ge ⟨i,rfl⟩
  choose q hq using hmem
  have hqinj : Function.Injective q := by
    intro i j hij
    apply B.injective
    rw [←hq i,←hq j,hij]
  let E := (Module.evalEquiv K D).trans B.dualBasis.equivFun
  have hE : ∀ (v : D) i, E v i = v.val (q i) := by
    intro v i
    change B.dualBasis.equivFun (Module.evalEquiv K D v) i = _
    rw [Basis.dualBasis_equivFun,←hq i]
    rfl
  let eb := Fintype.equivFin I
  refine ⟨Fintype.card I,fun j => q (eb.symm j),?_,?_,?_⟩
  · exact hqinj.comp eb.symm.injective
  · intro v w hvw
    apply E.injective
    funext i
    have h := congrFun hvw (eb i)
    simpa only [eb.symm_apply_apply,←hE] using h
  · intro z
    obtain ⟨v,hv⟩ := E.surjective (fun i => z (eb i))
    refine ⟨v,?_⟩
    funext j
    have h := congrFun hv (eb.symm j)
    simpa only [hE,eb.apply_symm_apply] using h

end
end Paper2.DegreeCSP.AffineSupportCoordinates
