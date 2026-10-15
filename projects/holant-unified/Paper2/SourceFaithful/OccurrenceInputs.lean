import Paper2.FixedFieldOutput.OccurrenceReductions
import Paper2.RelativeEO.Paper1OccurrenceAccepted
import Paper2.RelativeEO.Paper1BinaryAccepted

/-! Source-exact local Lemmas 3.1, 3.2 and 3.3 with canonical field outputs.
The retained graph, copying context and nonzero one-occurrence witness are
unchanged mathematical premises. Fixed root codes in those witness structures
are fixed constants, never a runtime answer conversion. -/
namespace Paper2.SourceFaithful
open Tractable ExactInput Problem RelativeEO
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup

structure Paper1BinaryInterpolationAccepted where
  infiniteOrder_3_1 : ∀ L : Language, Preprocessed L.family → BothChargeSigns L.family →
    ∀ B : Binary (K := AlgebraicComplex),
      (⟨2,matrixSignature B⟩ : AnySignature AlgebraicComplex) ∈ L.family →
      Matrix.det (transfer B) ≠ 0 → ¬ ProjectivelyFinite (transfer B) →
      ∃ (u v : Signature AlgebraicComplex 1) (M : Language), u ≠ 0 ∧ v ≠ 0 ∧
        M.family = insert (⟨2,Signature.tensor u v⟩ : AnySignature AlgebraicComplex) L.family ∧
        FixedFieldOutput.Reduces .nativeX M L

structure Paper1OccurrenceAccepted where
  universalPair_3_2 : ∀ L : Language,
    FixedFieldOutput.TaggedReduces .nativeX L directedPair (fun k => k ≤ 1) L
  replication_3_3 : ∀ (L : Language) (r s : ℕ)
    (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s),
    g ≠ 0 → h ≠ 0 → FixedFieldOutput.TaggedReduces .nativeX L g (fun k => k = 1) L →
    CarrierContext L g h → NonzeroTaggedClosure L g →
    ∀ M : Language, M.family = insert (⟨s,h⟩ : AnySignature AlgebraicComplex) L.family →
      FixedFieldOutput.Reduces .nativeX M L

 theorem replicate_directed_pair (P : Paper1OccurrenceAccepted) (L M : Language)
    (C : CarrierContext L directedPair directedPair)
    (hM : M.family = insert (⟨2,directedPair⟩ : AnySignature AlgebraicComplex) L.family) :
    FixedFieldOutput.Reduces .nativeX M L :=
  P.replication_3_3 L 2 2 directedPair directedPair directedPair_ne_zero directedPair_ne_zero
    (P.universalPair_3_2 L).exactly_one C (directedPairClosureCertificate L) M hM

end Paper2.SourceFaithful
