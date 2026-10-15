import Paper2.HeightOne.Cyclic.NormalizedFamilies
import Paper2.HeightOne.Cyclic.PortActions
import Paper2.HeightOne.PhaseCards.WalshProduct

/-! Odd-root normalization preserves actual tensor primality through separate
invertible diagonal actions on each original port. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhaseCards
open scoped BigOperators

def rootDiagonal (a : AlgebraicComplex) : Kernel AlgebraicComplex :=
  fun x y => if x = y then (if x then a else 1) else 0

lemma rootWeighted_coordinateAction {N : ℕ}
    (r : Fin 4 → rootsOfUnity N AlgebraicComplex) (q : Signature AlgebraicComplex 4) :
    rootWeighted r q = Signature.coordinateAction
      (fun j => rootDiagonal (r j).val) q := by
  funext x
  have he : x = ![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
  rw [he]
  simp only [rootWeighted,coe_rootWeight]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3
  all_goals simp [Signature.coordinateAction,rootDiagonal,sum_four_assignments,Fin.prod_univ_four]

lemma rootDiagonal_inverse (a : AlgebraicComplex) (ha : a ≠ 0) :
    Kernel.mul (rootDiagonal a⁻¹) (rootDiagonal a) = Signature.equality := by
  funext x y
  cases x <;> cases y <;> simp [Kernel.mul,rootDiagonal,Signature.equality,ha]

/-- Each dressed prime stays prime; there is no assertion of common-basis
transformability for the four independently chosen roots. -/
theorem tensorPrime_rootWeighted {N : ℕ}
    (r : Fin 4 → rootsOfUnity N AlgebraicComplex)
    (q : Signature AlgebraicComplex 4) (hq : TensorPrime q) :
    TensorPrime (rootWeighted r q) := by
  rw [rootWeighted_coordinateAction]
  apply tensorPrime_coordinateAction_ports _ (fun j => rootDiagonal (((r j).val : AlgebraicComplex)⁻¹)) _ hq
  intro j
  exact rootDiagonal_inverse _ (Units.ne_zero (r j).val)

theorem normalized_balanced_prime {N : ℕ}
    (f : Signature AlgebraicComplex 4) (hf : TensorPrime f)
    (r : Fin 4 → rootsOfUnity N AlgebraicComplex)
    (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex)
    (he : rootWeighted r (walshCoordinates f) = balancedWalsh p s) :
    TensorPrime (balancedWalsh p s) := by
  have hw := tensorPrime_action walshBasis.symm hf
  rw [walshBasis_inverse_action] at hw
  exact he ▸ tensorPrime_rootWeighted r _ hw

end
end Paper2.HeightOne.Cyclic
