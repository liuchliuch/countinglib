import Paper2.SourceFaithful.SourceStatements.PhaseProductParityBinary
import Paper2.SourceFaithful.SourceStatements.PhaseProductParityForms

/-! Exact zero-or-nonsingular interpretation of the local binary test.
There is no rank-one or disconnected two-unary alternative hidden in it. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards

theorem binary_phase_iff_pair {N : ℕ} (hN : 0 < N) {ι : Type} [Fintype ι]
    (hc : Fintype.card ι = 2) (g : Tensor AlgebraicComplex ι) :
    BinaryPhase N g ↔ g = 0 ∨ ∃ (a : ι → Bool) (κ η : AlgebraicComplex),
      κ ≠ 0 ∧ Root N η ∧ g = κ • twoPoint a (-η) := by
  classical
  let e : Fin 2 ≃ ι := (finCongr hc.symm).trans (Fintype.equivFin ι).symm
  have neq : ∀ a : ι → Bool, a ≠ fun i => !(a i) := by
    intro a he
    have hh := congrFun he (e 0)
    cases a (e 0) <;> simp at hh
  constructor
  · intro h
    by_cases hg : g = 0
    · exact Or.inl hg
    obtain ⟨a,ha⟩ : ∃ a, g a ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hg (funext hn)
    obtain ⟨_,_⟩ | ⟨η,hη,_,hcomp⟩ := h.2 a
    · contradiction
    right
    refine ⟨a,g a,η,ha,hη,?_⟩
    have supp : ∀ x, g x ≠ 0 → x = a ∨ x = fun i => !(a i) := by
      intro x hx
      have hp : parity (fun j => x (e j)) = parity (fun j => a (e j)) := by
        simpa only [parity,weight_reindex] using h.1 x a hx ha
      have cover : ∀ a x : Fin 2 → Bool, parity x = parity a →
          x = a ∨ x = fun i => !(a i) := by decide
      rcases cover _ _ hp with he | he
      · left; funext i; simpa using congrFun he (e.symm i)
      · right; funext i; simpa using congrFun he (e.symm i)
    funext x
    change g x = g a * (point a x + -η * point (fun i => !(a i)) x)
    by_cases hx : x = a
    · subst x; simp [point,neq]
    by_cases hxc : x = fun i => !(a i)
    · subst x; simp [point,hx,hcomp]; ring
    · have hz : g x = 0 := by
        by_contra hn
        exact (supp x hn).elim hx hxc
      simp [point,hx,hxc,hz]
  · rintro (rfl | ⟨a,κ,η,_,hη,rfl⟩)
    · exact ⟨hasParity_zero,fun _ => Or.inl ⟨rfl,rfl⟩⟩
    · have h := ((binaryPhase_twoPoint hN (fun j => a (e j)) (-η)
        (phaseRatio_one_negative hN hη)).reindex e).scale κ
      convert h using 1
      funext x
      simp only [Pi.smul_apply,smul_eq_mul,Tensor.reindex_apply,twoPoint,
        Pi.add_apply,point]
      have heq : (fun i => x (e i)) = (fun i => a (e i)) ↔ x = a := by
        constructor
        · intro he; funext i; simpa using congrFun he (e.symm i)
        · rintro rfl; rfl
      have hneq : (fun i => x (e i)) = (fun i => !(a (e i))) ↔ x = fun i => !(a i) := by
        constructor
        · intro he; funext i; simpa using congrFun he (e.symm i)
        · rintro rfl; rfl
      simp only [heq,hneq]

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity
