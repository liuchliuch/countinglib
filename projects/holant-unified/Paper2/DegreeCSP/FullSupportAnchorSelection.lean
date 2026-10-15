import Paper2.DegreeCSP.FullSupportBinaryWitness
import Paper2.DegreeCSP.GeneratedSignAnchor
import Paper2.DegreeCSP.GeneratedPhaseRemoval

/-! Select an actual scaled Hadamard anchor from a genuinely generated,
full-support nonproduct table. Neither a signed anchor nor an affine phase
classification is supplied as a hypothesis. -/
namespace Paper2.DegreeCSP.FullSupportAnchorSelection
open scoped BigOperators
open Tractable TensorDecomposition AxisRatioSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem sign_nonconstant {n : ℕ} (f : Signature AlgebraicComplex n)
    (hnot : ¬Product f) (c : AlgebraicComplex) (phi : Fin n→AlgebraicComplex)
    (P : (Fin n→Bool)→Bool)
    (hform : ∀x,f x=c*(∏i,if x i then phi i else 1)*(if P x then -1 else 1)) :
    ∃x,P x=true := by
  classical
  by_contra none
  apply hnot
  apply GeneratedSignAnchor.product_of_zero_sign f c phi P ?_ hform
  intro x
  cases hx:P x
  · rfl
  · exact (none ⟨x,hx⟩).elim

theorem exists_anchor {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (hp0 : Generated F k (literalPin false)) (hp1 : Generated F k (literalPin true))
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (hne : ∀x,f x≠0) (hnot : ¬Product f) :
    ∃a:AlgebraicComplex,a≠0 ∧ Generated F k (GeneratedHadamardUnary.anchor a) := by
  classical
  obtain ⟨hphi,P,hzero,hform⟩ := generated_full_support_signs hBO f hf hne
  have haxes := GeneratedPhaseRemoval.sign_axis_zero f hne P hform
  have hex := sign_nonconstant f hnot (f zeroWord) (axisRatio f) P hform
  obtain ⟨z,i,j,hij,hqne,_,hdet⟩ := FullSupportBinaryWitness.exists_signed_binary
    f (f zeroWord) (hne _) (axisRatio f) hphi P hzero haxes hex hform
  let q : Signature AlgebraicComplex 2 := FullSupportBinaryWitness.coefficientTable f z i j
  have hq : Generated F k q := by
    let r : Fin n→Option (Fin 2) := fun l=>if l=i then some 0 else if l=j then some 1 else none
    obtain ⟨R,hR,hdiv,hvalue⟩ := generated_restrict hf hp0 hp1 r z
    refine ⟨R,hR,hdiv,?_⟩
    rw [hvalue]
    funext x
    congr 1
    funext l
    by_cases hli:l=i
    · subst l; simp [r,Function.update,hij]
    by_cases hlj:l=j
    · subst l; simp [r,Function.update,hli]
    · simp [r,Function.update,hli,hlj]
  have hqc : ∀b d,(q ![b,d] : ℂ)≠0 := by
    intro b d
    exact_mod_cast hqne ![b,d]
  have hb := OriginalBO.generated_binary_bo hBO q hq
  have hb2 := OriginalBO.generated_binary_bo hBO (fun x=>q x^2) (generated_pow hq 2)
  have hb2c : OriginalBO.BlockOrthogonal (fun b d=>(q ![b,d] : ℂ)^2) := by
    convert hb2 using 1

  have hbt := OriginalBO.generated_binary_transpose_bo hBO q hq
  rcases OriginalBO.binary_phase_alternative (fun b d=>(q ![b,d] : ℂ)) hqc hb hb2c hbt with
    hz | ⟨_,_,hu,hv,hun,hvn,hchart⟩
  · exact (hdet hz).elim
  · have ha : (q ![false,false] : ℂ)≠0 := hqc false false
    have hphase := GeneratedPhaseRemoval.axis_eighth hBO q hq
      (q ![false,false] : ℂ) (OriginalBO.firstPhase (fun b d=>(q ![b,d] : ℂ)))
      (OriginalBO.secondPhase (fun b d=>(q ![b,d] : ℂ))) ha hu hv hchart f hf hp0 hne
    obtain ⟨S,c,hc,hszero,hS,hSform⟩ := GeneratedPhaseRemoval.signs hBO f hf hp0 hne hphase
    have hsaxis := GeneratedPhaseRemoval.sign_axis_zero f hne S hSform
    have hsex := sign_nonconstant f hnot (f zeroWord) (axisRatio f) S hSform
    exact ⟨c,hc,GeneratedSignAnchor.generated_anchor c S hS hp0 hp1 hszero hsaxis hsex⟩

end
end Paper2.DegreeCSP.FullSupportAnchorSelection
