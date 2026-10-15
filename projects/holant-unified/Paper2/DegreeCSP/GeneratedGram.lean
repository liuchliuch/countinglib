import Paper2.DegreeCSP.GeneratedCompose
import Paper2.DegreeCSP.GeneratedPullback
import Paper2.DegreeCSP.GramPhaseConstraint
import Paper2.DegreeCSP.BinaryPhaseChart
import Paper2.DegreeCSP.OrthogonalityScaling

/-! A binary Gram table is formed with actual shared variables and an actual
hidden Boolean sum. All degree divisibility conditions survive unchanged. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace GeneratedGram

def gram (f : Signature AlgebraicComplex 2) : Signature AlgebraicComplex 2 :=
  fun x => ∑ b : Bool,f ![x 0,b]*f ![x 1,b]

theorem generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    {f : Signature AlgebraicComplex 2} (hf : Generated F k f) :
    Generated F k (gram f) := by
  have hl := generated_pullback hf (![0,2] : Fin 2 → Fin 3)
  have hr := generated_pullback hf (![1,2] : Fin 2 → Fin 3)
  have h := generated_sum_last (generated_hadamard hl hr)
  have he : (fun x : Fin 2 → Bool => ∑ b : Bool,
      f (fun i => Fin.snoc (α := fun _ => Bool) x b (![0,2] i)) *
      f (fun i => Fin.snoc (α := fun _ => Bool) x b (![1,2] i))) = gram f := by
    funext x
    apply Finset.sum_congr rfl
    intro b _
    congr 2 <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact h

private theorem gram_chart (f : Signature AlgebraicComplex 2) (a u v : ℂ)
    (h : ∀ b c,(f ![b,c] : ℂ)=OriginalBO.phaseChart a u v b c) (b c : Bool) :
    (gram f ![b,c] : ℂ) = a^2*OriginalBO.weightedGram u (v^2) b c := by
  simp only [gram,Fintype.sum_bool,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  rw [h b false,h c false,h b true,h c true]
  cases b <;> cases c <;> simp [OriginalBO.phaseChart,OriginalBO.weightedGram] <;> ring

/-- The actual Gram and its square quantize the retained second phase. This is
only the displayed eighth-power constraint, not a shared-phase classification. -/
theorem second_phase_eighth {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (f : Signature AlgebraicComplex 2) (hf : Generated F k f)
    (a u v : ℂ) (ha : a ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ∀ b c,(f ![b,c] : ℂ)=OriginalBO.phaseChart a u v b c) : v^8=1 := by
  have hg : Generated F k (gram f) := generated hf
  have hGram := OriginalBO.generated_binary_bo hBO (gram f) hg
  have hGram2 := OriginalBO.generated_binary_bo hBO (fun x => gram f x ^ 2)
    (generated_pow hg 2)
  have hW : OriginalBO.BlockOrthogonal (OriginalBO.weightedGram u (v^2)) := by
    apply (OriginalBO.block_orthogonal_scale (a^2) (pow_ne_zero 2 ha) _).mp
    convert hGram using 1
    funext b c
    exact (gram_chart f a u v h b c).symm
  have hW2 : OriginalBO.BlockOrthogonal (fun b c => OriginalBO.weightedGram u (v^2) b c ^ 2) := by
    apply (OriginalBO.block_orthogonal_scale (a^4) (pow_ne_zero 4 ha) _).mp
    convert hGram2 using 1
    funext b c
    push_cast
    rw [gram_chart f a u v h]
    ring
  rcases OriginalBO.weighted_gram_phase u (v^2) hu hW hW2 with hz | hroot
  · exact False.elim ((pow_ne_zero 2 hv) hz)
  · simpa only [← pow_mul] using hroot

/-- Swapping the original two boundary ports gives the same bound on the first
phase, with no additional label or field element. -/
theorem both_phase_eighth {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (f : Signature AlgebraicComplex 2) (hf : Generated F k f)
    (a u v : ℂ) (ha : a ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ∀ b c,(f ![b,c] : ℂ)=OriginalBO.phaseChart a u v b c) :
    u^8=1 ∧ v^8=1 := by
  let fT : Signature AlgebraicComplex 2 := fun x => f ![x 1,x 0]
  have hfT : Generated F k fT := by
    have ht := generated_pullback hf (![1,0] : Fin 2 → Fin 2)
    have he : (fun x => f (fun i => x (![1,0] i))) = fT := by
      funext x
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [he] at ht
    exact ht
  have hT (b c : Bool) : (fT ![b,c] : ℂ)=OriginalBO.phaseChart a v u b c := by
    change (f ![c,b] : ℂ) = _
    rw [h c b]
    cases b <;> cases c <;> simp [OriginalBO.phaseChart] <;> ring
  exact ⟨second_phase_eighth hBO fT hfT a v u ha hv hu hT,
    second_phase_eighth hBO f hf a u v ha hu hv h⟩

end GeneratedGram
end
end Paper2.DegreeCSP
