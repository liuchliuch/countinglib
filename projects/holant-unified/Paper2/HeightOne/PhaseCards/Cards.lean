import Paper2.HeightOne.PhaseCards.Representatives
import Paper2.HeightOne.PhaseCards.WalshTransport
import Paper2.HeightOne.PhaseCards.ActualContraction

/-! A fixed choice of genuine binary cards for every root phase in the complete
normalized class group, and their actual contraction witnesses. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable GroupSplit GroupSplit.MatrixGroup EndpointSelfLoop

structure RotationCards (F : SignatureFamily AlgebraicComplex) (N : ℕ) where
  binary : rootsOfUnity N AlgebraicComplex → AMat
  scale : rootsOfUnity N AlgebraicComplex → AlgebraicComplex
  actual : ∀ s, ActualNonsingular F (binary s)
  scale_ne_zero : ∀ s, scale s ≠ 0
  transfer_eq : ∀ s, transfer (binary s) = scale s • phase s.val

/-- These choices are taken from all actual group classes, not from a substitute
finite gadget enumeration. -/
theorem rotationCards_nonempty {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N ∨
      actualClasses F = dihedralPhaseClasses N) : Nonempty (RotationCards F N) := by
  have h : ∀ s : rootsOfUnity N AlgebraicComplex,
      ∃ (B : AMat) (c : AlgebraicComplex), ActualNonsingular F B ∧ c ≠ 0 ∧
        transfer B = c • phase s.val := by
    intro s
    apply actual_rotation
    rcases hG with hG | hG
    · rw [hG]; exact ⟨s.val, s.property, rfl⟩
    · rw [hG]; exact Or.inl ⟨s.val, s.property, rfl⟩
  choose B c hB hc ht using h
  exact ⟨⟨B, c, hB, hc, ht⟩⟩

namespace RotationCards
variable {F : SignatureFamily AlgebraicComplex} {N : ℕ}
variable {ι : Type} [Fintype ι]

/-- The native-X network obtained by putting the fixed actual rotation binary
on the ordered distinct pair. -/
def contraction (C : RotationCards F N) (a b : ι) (hab : a ≠ b)
    (s : rootsOfUnity N AlgebraicComplex) (f : Tensor AlgebraicComplex ι) :=
  card (nativeKernel (C.binary s)) a b hab f

theorem realizable (C : RotationCards F N) (a b : ι) (hab : a ≠ b)
    (s : rootsOfUnity N AlgebraicComplex) {f : Tensor AlgebraicComplex ι}
    (hf : NetworkRealizable F f) : NetworkRealizable F (C.contraction a b hab s f) :=
  actual_contractKernel (hf.reindex (splitPorts a b hab)) (C.actual s).1

theorem walsh (C : RotationCards F N) (a b : ι) (hab : a ≠ b)
    (s : rootsOfUnity N AlgebraicComplex) (f : Tensor AlgebraicComplex ι) :
    walshCoordinates (C.contraction a b hab s f) =
      (2 * C.scale s) • HeightOne.plusContraction a b hab (s.val : AlgebraicComplex) (walshCoordinates f) :=
  rotation_card_walsh a b hab f (C.transfer_eq s)

lemma walsh_scale_ne_zero (C : RotationCards F N) (s : rootsOfUnity N AlgebraicComplex) :
    2 * C.scale s ≠ 0 := mul_ne_zero (by norm_num) (C.scale_ne_zero s)

end RotationCards
end
end Paper2.HeightOne.PhaseCards
