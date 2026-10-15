import Paper2.HeightOne.PhaseCards.Coordinates

/-! The source's Walsh contraction equation, including the exact representative
scale and the factor two from the native-X edge convention. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
attribute [local instance] Classical.propDecidable
open Tractable GroupSplit GroupSplit.MatrixGroup EndpointSelfLoop
open scoped BigOperators
variable {ι : Type} [Fintype ι]

/-- Analytic Walsh coefficients, with no claim of gadget realizability. -/
def walshCoordinates (f : Tensor AlgebraicComplex ι) : Tensor AlgebraicComplex ι :=
  action walshInv f

lemma walsh_action_cancel (f : Tensor AlgebraicComplex ι) :
    action walsh (walshCoordinates f) = f := by
  apply action_cancel
  have h := walsh_mul_walshInv
  exact h

lemma walsh_inv_action_cancel (f : Tensor AlgebraicComplex ι) :
    walshCoordinates (action walsh f) = f := by
  apply action_cancel
  exact walshInv_mul_walsh

lemma walshCoordinates_reindex {κ : Type} [Fintype κ]
    (e : ι ≃ κ) (f : Tensor AlgebraicComplex ι) :
    walshCoordinates (Tensor.reindex e f) = Tensor.reindex e (walshCoordinates f) :=
  action_reindex _ _ _

lemma walshCoordinates_contract (E : Kernel AlgebraicComplex)
    (f : Tensor AlgebraicComplex (ι ⊕ Bool)) :
    walshCoordinates (contractKernel E f) =
      contractKernel (Kernel.pullback E walsh) (walshCoordinates f) := by
  have h := contractKernel_action E walsh (walshCoordinates f)
  rw [walsh_action_cancel] at h
  rw [h, walsh_inv_action_cancel]

/-- Literal ordered contraction at distinct original port occurrences. -/
def card (E : Kernel AlgebraicComplex) (a b : ι) (hab : a ≠ b)
    (f : Tensor AlgebraicComplex ι) : Tensor AlgebraicComplex (Remaining a b) :=
  contractKernel E (Tensor.reindex (splitPorts a b hab) f)

lemma walshCoordinates_card (E : Kernel AlgebraicComplex)
    (a b : ι) (hab : a ≠ b) (f : Tensor AlgebraicComplex ι) :
    walshCoordinates (card E a b hab f) =
      card (Kernel.pullback E walsh) a b hab (walshCoordinates f) := by
  unfold card
  rw [walshCoordinates_contract, walshCoordinates_reindex]

lemma contractKernel_scale (c : AlgebraicComplex) (E : Kernel AlgebraicComplex)
    (f : Tensor AlgebraicComplex (ι ⊕ Bool)) :
    contractKernel (c • E) f = c • contractKernel E f := by
  funext x
  simp only [contractKernel, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma card_plus (s : AlgebraicComplex) (a b : ι) (hab : a ≠ b)
    (f : Tensor AlgebraicComplex ι) :
    card (plusKernel s) a b hab f = HeightOne.plusContraction a b hab s f := by
  funext x
  unfold card contractKernel HeightOne.plusContraction
  calc
    _ = ∑ p : Bool × Bool, HeightOne.plusKernel s p.1 p.2 *
        f (extendBits a b hab x p.1 p.2) := by
      apply Fintype.sum_equiv (Equiv.boolArrowEquivProd Bool)
      intro v
      congr 1
      congr 1
      funext i
      cases i with
      | inl j => rfl
      | inr c => cases c <;> rfl
    _ = _ := Fintype.sum_prod_type _

/-- The precise Walsh formula for a real rotation binary attached by two X
edges. It retains the original surviving port order and the actual scale 2c. -/
theorem rotation_card_walsh (a b : ι) (hab : a ≠ b)
    (f : Tensor AlgebraicComplex ι) {B : AMat} {c s : AlgebraicComplex}
    (hB : transfer B = c • phase s) :
    walshCoordinates (card (nativeKernel B) a b hab f) =
      (2 * c) • HeightOne.plusContraction a b hab s (walshCoordinates f) := by
  rw [walshCoordinates_card]
  have he : Kernel.pullback (nativeKernel B) walsh = (2 * c) • plusKernel s :=
    rotation_analysis_kernel hB
  rw [he]
  unfold card
  rw [contractKernel_scale]
  congr 1
  exact card_plus s a b hab _

end
end Paper2.HeightOne.PhaseCards
