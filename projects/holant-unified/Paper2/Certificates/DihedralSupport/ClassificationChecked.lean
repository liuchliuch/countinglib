module
public import Paper2.Certificates.DihedralSupport.ClassificationSemantics
public import Mathlib.Data.Finset.Card

/-! Kernel-checked properties of the literal survivor rows, separate from the generic coverage proof. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport

def survivorMasks : Finset Nat := ((List.range 873).map survivorAt).toFinset


instance (m : Nat) : Decidable (AdmissibleMask m) := by
  unfold AdmissibleMask
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem survivors_admissible_checked :
    ∀ i : Fin 873, AdmissibleMask (survivorAt i.val) := by decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem survivorMasks_card : survivorMasks.card = 873 := by decide +kernel


end Paper2.Certificates.DihedralSupport
