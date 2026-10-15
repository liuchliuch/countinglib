import Paper2.RelativeEO.GramNetwork
import Paper2.RelativeEO.ARSPrimeDecomposition

/-! A rank-one two-port slice relation is an actual ordered tensor split of
the original signature. Coordinate slices are used only to prove this identity,
never treated as available pinning gadgets. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable EndpointSelfLoop
noncomputable section
variable {n : ℕ}

/-- Enumerate the exposed binary first and every remaining port exactly once. -/
def gramFactorPorts (i j : Fin n) (hij : i ≠ j) :
    Fin (2 + Fintype.card (Remaining i j)) ≃ Fin n :=
  (finSumFinEquiv.symm.trans
    (Equiv.sumCongr finTwoEquiv (Fintype.equivFin (Remaining i j)).symm)).trans
      ((Equiv.sumComm Bool (Remaining i j)).trans (splitPorts i j hij).symm)

@[simp] theorem gramFactorPorts_first (i j : Fin n) (hij : i ≠ j) (b : Fin 2) :
    gramFactorPorts i j hij (Fin.castAdd (Fintype.card (Remaining i j)) b) =
      if finTwoEquiv b then j else i := by
  simp [gramFactorPorts,splitPorts]

@[simp] theorem gramFactorPorts_rest (i j : Fin n) (hij : i ≠ j)
    (k : Fin (Fintype.card (Remaining i j))) :
    gramFactorPorts i j hij (Fin.natAdd 2 k) =
      ((Fintype.equivFin (Remaining i j)).symm k).val := by
  simp [gramFactorPorts,splitPorts]

/-- Vanishing equal-bit slices and proportional opposite-bit slices give a
literal binary tensor factor with all original ports and coefficients retained. -/
theorem gram_slices_tensor_factor (i j : Fin n) (hij : i ≠ j)
    (f : Signature AlgebraicComplex n) (r : AlgebraicComplex)
    (h00 : ∀ z, pairSlice i j hij f false false z = 0)
    (h11 : ∀ z, pairSlice i j hij f true true z = 0)
    (hr : ∀ z, pairSlice i j hij f false true z = r * pairSlice i j hij f true false z) :
    Tensor.reindex (gramFactorPorts i j hij)
      (Signature.tensor (eoSignature r 1)
        (fun z : Fin (Fintype.card (Remaining i j)) → Bool =>
          pairSlice i j hij f true false (fun k => z ((Fintype.equivFin (Remaining i j)) k)))) = f := by
  funext x
  have he : f x = WeightedMatching.binary r 1 (x i) (x j) *
      pairSlice i j hij f true false (fun k => x k.val) := by
    have hx : f x = pairSlice i j hij f (x i) (x j) (fun k => x k.val) :=
      congrArg f (fillPair_eta i j hij x).symm
    rw [hx]
    cases hi : x i <;> cases hj : x j <;>
      simp [h00,h11,hr,WeightedMatching.binary]
  rw [he]
  change eoSignature r 1 (fun b => x (gramFactorPorts i j hij (Fin.castAdd _ b))) *
    pairSlice i j hij f true false (fun k =>
      x (gramFactorPorts i j hij (Fin.natAdd 2 ((Fintype.equivFin (Remaining i j)) k)))) = _
  simp only [gramFactorPorts_first,gramFactorPorts_rest,Equiv.symm_apply_apply]
  congr 1

/-- A positive residual block contradicts genuine tensor primality. -/
theorem gram_slices_not_prime (i j : Fin n) (hij : i ≠ j) (hn : 4 ≤ n)
    (f : Signature AlgebraicComplex n) (r : AlgebraicComplex)
    (h00 : ∀ z, pairSlice i j hij f false false z = 0)
    (h11 : ∀ z, pairSlice i j hij f true true z = 0)
    (hr : ∀ z, pairSlice i j hij f false true z = r * pairSlice i j hij f true false z) :
    ¬ TensorPrime f := by
  intro hp
  have hc : Fintype.card (Remaining i j) + 2 = n := by
    have h := Fintype.card_congr (splitPorts i j hij)
    simpa only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] using h.symm
  exact hp.2 2 (Fintype.card (Remaining i j)) (by decide) (by omega)
    (gramFactorPorts i j hij) (eoSignature r 1) _
    (gram_slices_tensor_factor i j hij f r h00 h11 hr)

end
end Paper2.RelativeEO
