import Paper2.Paper1ProvedReplicationFields
import Paper2.Paper1ProvedReplicationControl

/-! The two official occurrence lemmas now have actual controlled programmes.
The generic copying theorem consumes its exact three source premises: a proved
one-occurrence reduction, the retained native copying context, and the literal
nonzero one-occurrence closure. No ambient classification is supplied. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem replication (L : Language) {r s : ℕ} (g : Signature AlgebraicComplex r)
     (h : Signature AlgebraicComplex s)
     (one : FixedFieldOutput.TaggedReduces .nativeX L g (fun k => k=1) L)
     (C : CarrierContext L g h) (Z : NonzeroTaggedClosure L g)
     (M : Language) (hM : M.family=insert (⟨s,h⟩ : AnySignature AlgebraicComplex) L.family) :
     FixedFieldOutput.Reduces .nativeX M L := by
   have hr := ReplicationControl.reducesOfPartition L g h C Z
     (ReplicationFields.presentation L g h C) (ReplicationFields.embedding L g h C)
     Subtype.val_injective (ReplicationFields.scale L g h C) (ReplicationFields.closureValue L g h C Z)
     (ReplicationFields.scale_nonzero L g h C) (ReplicationFields.closure_nonzero L g h C Z)
     (ReplicationFields.sourceValue L g h C Z) (ReplicationFields.targetValue L g h C)
     (ReplicationFields.targetBound L g h C) (ReplicationFields.source_correct L g h C Z)
     (ReplicationFields.target_correct L g h C) (ReplicationFields.partition L g h C Z) one
   have hi : M.family ⊆ (tagged L h).family := by rw [hM,tagged_family]
   exact (restriction M (tagged L h) hi).trans hr

 theorem occurrenceProvider : SourceFaithful.Paper1OccurrenceAccepted where
   universalPair_3_2 := universalPair
   replication_3_3 := fun L _ _ g h _ _ one C Z M hM => replication L g h one C Z M hM

end
end Paper2.Paper1Proved
