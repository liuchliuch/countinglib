import Paper2.RelativeEO.ARSPrimeDecomposition
import Paper2.RelativeEO.MatchingFactors

/-! Reassemble a decomposition consisting entirely of binary EO/projective-ARS
factors into the exact source B_ARS class, preserving every ordered port. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open scoped BigOperators

/-- Canonically oriented coefficient form, with no complex-only parameters. -/
theorem binary_ars_form (f : Signature AlgebraicComplex 2) (hf : f ≠ 0)
    (he : Signature.CentralSupport f) (hs : ProjectiveARS f) :
    ∃ c a : AlgebraicComplex, c ≠ 0 ∧ a ≠ 0 ∧
      f = fun x => c * eoSignature a (conjugateAlgebraic a) x := by
  let p := f (binWord false true)
  let q := f (binWord true false)
  have hform : f = eoSignature p q := binary_central_form f he
  have hp : p ≠ 0 := by
    intro hp
    have hq : q = 0 := by
      by_contra hq
      have hh := hs.complement_nonzero (binWord true false) hq
      have hw : (fun i => !(binWord true false i)) = binWord false true := by
        funext i; fin_cases i <;> rfl
      exact hh (by rw [hw]; exact hp)
    exact hf (by rw [hform,hp,hq,eoSignature_zero])
  obtain ⟨c,a,hc,ha,hp',hq'⟩ := binary_ars_coefficients p q hp (hform ▸ hs)
  refine ⟨c,a,hc,ha,?_⟩
  rw [hform]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [eoSignature,matrixSignature,eoMatrix,h0,h1,hp',hq']

/-- All actual arity-two factors assemble into one literal oriented matching. -/
theorem binary_decomposition_isARSProduct {n : ℕ}
    (D : TensorDecomposition AlgebraicComplex n)
    (h₂ : ∀ i, D.arity i = 2) (hn : ∀ i, D.factor i ≠ 0)
    (he : ∀ i, Signature.CentralSupport (D.factor i))
    (hs : ∀ i, ProjectiveARS (D.factor i)) : IsARSProduct D.value := by
  classical
  let e : (i : Fin D.count) → Fin 2 ≃ Fin (D.arity i) := fun i => finCongr (h₂ i).symm
  let g : Fin D.count → Signature AlgebraicComplex 2 :=
    fun i => Tensor.reindex (e i).symm (D.factor i)
  have hg (i : Fin D.count) : g i ≠ 0 := by
    intro hz
    apply hn i
    have hh := congrArg (Tensor.reindex (e i)) hz
    funext x
    simpa only [g,Tensor.reindex,Equiv.apply_symm_apply,Pi.zero_apply] using congrFun hh x
  have hge (i : Fin D.count) : Signature.CentralSupport (g i) :=
    centralSupport_reindex (he i) (e i).symm
  have hgs (i : Fin D.count) : ProjectiveARS (g i) := (hs i).reindex (e i).symm
  choose c a hc ha hform using fun i => binary_ars_form (g i) (hg i) (hge i) (hgs i)
  let P : OrientedPerfectPairing n := {
    count := D.count
    ports := ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans
      (Equiv.sigmaEquivProd (Fin D.count) (Fin 2)).symm).trans
      ((Equiv.sigmaCongrRight e).trans D.ports) }
  refine ⟨P,a,(D.scale : AlgebraicComplex) * ∏ i,c i,
    mul_ne_zero D.scale.ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hc i)),ha,?_⟩
  funext x
  have hfac (i : Fin D.count) : D.factor i (fun j => x (D.ports ⟨i,j⟩)) =
      c i * WeightedMatching.binary (a i) (conjugateAlgebraic (a i))
        (x (P.ports (i,false))) (x (P.ports (i,true))) := by
    have hh := congrFun (hform i) (fun j => x (D.ports ⟨i,e i j⟩))
    change _ = c i * eoSignature (a i) (conjugateAlgebraic (a i))
      (fun j => x (D.ports ⟨i,e i j⟩))
    simpa only [g,Tensor.reindex,Equiv.apply_symm_apply] using hh
  simp only [TensorDecomposition.value,WeightedMatching.product,hfac,Finset.prod_mul_distrib]
  ring

end Paper2.RelativeEO
