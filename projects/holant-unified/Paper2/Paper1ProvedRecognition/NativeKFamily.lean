import Paper2.Paper1ProvedRecognition.Source
import Paper2.ExactInput.Recognition.NativeTargetData

/-! The forward K table family needed by native criterion recognition. The
target descriptors remain arbitrary represented choices at the literal flat
lookup addresses. The whole family is exactly K times the original family,
with every original row, arity and port order retained. -/
namespace Paper2.Paper1ProvedRecognition.NativeKFamily
open Paper2.ExactInput
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Paper2.ExactInput.Recognition.NativeTargetPacking
noncomputable section

/-- The prescribed forward transformation acts once at each original port. -/
def tables (L : Language) (i : Fin (data L).count) :
    Holant.Signature Holant.Tractable.AlgebraicComplex ((data L).arity i) :=
  Paper2.Tractable.sourceKBasis.action ((data L).G i)

/-- The represented target data has precisely the native criterion's family.
No inverse K, rowwise choice of basis, or scalar normalization is inserted. -/
theorem target_family (L : Language) (cs : List Root)
    (hrep : ∀ i x,
      (cs.getD (targetOrdinal (data L) i x) defaultRoot).Represents
        (tables L i x : ℂ)) :
    RuntimeSevenDecision.family (targetData (data L) (tables L) cs hrep) =
      Paper2.kImage L := by
  have hf : RuntimeSevenDecision.family
      (targetData (data L) (tables L) cs hrep) =
      Paper2.Tractable.familyAction Paper2.Tractable.sourceKBasis
        (RuntimeSevenDecision.family (data L)) := by
    ext f
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨⟨(data L).arity i,(data L).G i⟩,⟨i,rfl⟩,rfl⟩
    · rintro ⟨g,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
  rw [hf,data_family]
  rfl

/-- The physical reshape is the literal packed input of the represented
forward-K tables on every original row. -/
theorem target_packed (L : Language) (cs : List Root)
    (hrep : ∀ i x,
      (cs.getD (targetOrdinal (data L) i x) defaultRoot).Represents
        (tables L i x : ℂ)) :
    reshape (RuntimeSupportTable.original (data L),cs) =
      RuntimeSupportTable.original (targetData (data L) (tables L) cs hrep) :=
  targetData_original (data L) (tables L) cs hrep

end
end Paper2.Paper1ProvedRecognition.NativeKFamily

