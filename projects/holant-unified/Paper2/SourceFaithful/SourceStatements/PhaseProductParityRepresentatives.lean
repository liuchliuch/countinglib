import Paper2.SourceFaithful.SourceStatements.PhaseProductParityScalars
import Paper2.SourceFaithful.SourceStatements.CyclicDressingStatement

/-! The specified ordered representatives in source Lemma 5.12. A literal
Walsh matrix κ_s D_s Z contributes the exact analysis kernel 4κ_s K_s^+;
the two native X edges and unnormalised Walsh matrix account for the four. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup

def RepresentativeCyclicContractions (N : ℕ) (B : AlgebraicComplex → AMat)
    (f : Signature AlgebraicComplex 4) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (s : AlgebraicComplex), Root N s →
    SupportedOnParity (card (analysisKernel (B s)) i j hij f) 0 ∧
      ∀ x, RootComplement N (card (analysisKernel (B s)) i j hij f x)
        (card (analysisKernel (B s)) i j hij f (fun k => !(x k)))

lemma representative_card {B : AMat} {κ s : AlgebraicComplex}
    (hB : walshBinary B = κ • PhaseCards.plusKernel s)
    (i j : Fin 4) (hij : i ≠ j) (f : Signature AlgebraicComplex 4) :
    card (analysisKernel B) i j hij f = (4 * κ) • plusContraction i j hij s f := by
  have ha := rotation_analysis_kernel (CyclicDressing.transfer_of_walshBinary hB)
  have ha' : analysisKernel B = (4 * κ) • PhaseCards.plusKernel s := by
    rw [show 2 * (2 * κ) = 4 * κ by ring] at ha
    exact ha
  rw [ha']
  change contractKernel ((4 * κ) • PhaseCards.plusKernel s)
      (Tensor.reindex (EndpointSelfLoop.splitPorts i j hij) f) = _
  rw [contractKernel_scale]
  exact congrArg (fun t => (4 * κ) • t) (card_plus s i j hij f)

theorem source_5_12_representatives {N : ℕ} (hN : 3 ≤ N)
    (B : AlgebraicComplex → AMat) (κ : AlgebraicComplex → AlgebraicComplex)
    (hκ : ∀ s, Root N s → κ s ≠ 0)
    (hB : ∀ s, Root N s → walshBinary (B s) = κ s • PhaseCards.plusKernel s)
    (f : Signature AlgebraicComplex 4) (heven : SupportedOnParity f 0) :
    RepresentativeCyclicContractions N B f ↔
      CyclicNormalForm N (f (fun _ => false)) (f (fun _ => true))
        (fun i => f (centralWord i (fun _ => false)))
        (fun i => f (flipAll (centralWord i (fun _ => false)))) := by
  have hc : ∀ (i j : Fin 4) s, Root N s → (fun _ _ s => 4 * κ s) i j s ≠ 0 :=
    fun _ _ s hs => mul_ne_zero (by norm_num) (hκ s hs)
  rw [← source_5_12_scaled hN (fun _ _ s => 4 * κ s) hc f heven]
  unfold RepresentativeCyclicContractions ScaledCyclicContractions
  constructor <;> intro h i j hij s hs
  · simpa only [representative_card (hB s hs)] using h i j hij s hs
  · simpa only [representative_card (hB s hs)] using h i j hij s hs

def NativeCyclicContractions (N : ℕ) (B : AlgebraicComplex → AMat)
    (f : Signature AlgebraicComplex 4) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (s : AlgebraicComplex), Root N s →
    SupportedOnParity (walshCoordinates (card (nativeKernel (B s)) i j hij f)) 0 ∧
      ∀ x, RootComplement N
        (walshCoordinates (card (nativeKernel (B s)) i j hij f) x)
        (walshCoordinates (card (nativeKernel (B s)) i j hij f) (fun k => !(x k)))

lemma native_card_walsh (B : AMat) (i j : Fin 4) (hij : i ≠ j)
    (f : Signature AlgebraicComplex 4) :
    walshCoordinates (card (nativeKernel B) i j hij f) =
      card (analysisKernel B) i j hij (walshCoordinates f) := by
  rw [walshCoordinates_card]
  rfl

theorem source_5_12_native {N : ℕ} (hN : 3 ≤ N)
    (B : AlgebraicComplex → AMat) (κ : AlgebraicComplex → AlgebraicComplex)
    (hκ : ∀ s, Root N s → κ s ≠ 0)
    (hB : ∀ s, Root N s → walshBinary (B s) = κ s • PhaseCards.plusKernel s)
    (f : Signature AlgebraicComplex 4)
    (heven : SupportedOnParity (walshCoordinates f) 0) :
    NativeCyclicContractions N B f ↔
      CyclicNormalForm N (walshCoordinates f (fun _ => false))
        (walshCoordinates f (fun _ => true))
        (fun i => walshCoordinates f (centralWord i (fun _ => false)))
        (fun i => walshCoordinates f (flipAll (centralWord i (fun _ => false)))) := by
  rw [← source_5_12_representatives hN B κ hκ hB (walshCoordinates f) heven]
  unfold NativeCyclicContractions RepresentativeCyclicContractions
  simp only [native_card_walsh]

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity
