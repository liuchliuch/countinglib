import Paper2.Paper1ProvedOccurrenceAdapters
import Paper2.Paper1ProvedGadgetProvider

/-! The copying context is serialized with the original family's labels shifted
by one. It therefore uses no designated carrier vertex, even when an original
signature happens to equal the carrier table. -/
namespace Paper2.Paper1Proved.ReplicationTemplates
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
open Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable (L : Language) {r s : ℕ}
variable (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s)
variable (C : CarrierContext L g h)

theorem tagged_arity (i : ℕ) : (tagged L g).arity i=if i=0 then r else L.arity (i-1) := by
  cases i with
  | zero => rfl
  | succ i => simp

def contextLabels : Labelling (sourceShape C.graph.shape) (L.count+1) 1 (tagged L g).arity where
  vertex v := (vertexLabel L C.graph C.uses v).succ
  vertex_arity v := by
    change (tagged L g).arity ((vertexLabel L C.graph C.uses v).val+1)=C.graph.shape.arity v
    rw [tagged_arity_succ]
    exact congrArg Sigma.fst (vertexLabel_literal L C.graph C.uses v)
  edge _ := 0

abbrev contextTemplate : Template := (contextLabels L g h C).template

theorem contextDenote :
    ((contextTemplate L g h C).network (contextLabels L g h C).wellFormed
      (signatures (tagged L g)) (kernels .nativeX)).denote=C.graph.denote := by
  rw [← sourceNetwork_denote C.graph]
  apply Labelling.denote_template_of_labels
  · intro v x
    let j := vertexLabel L C.graph C.uses v
    have ht := (tagged_succ L g j).trans (vertexLabel_literal L C.graph C.uses v)
    exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      ((tagged L g).signature j.succ) (C.graph.vertex v) ht (congrArg Sigma.fst ht) x
  · intro e a b
    exact (congrFun (congrFun (C.nativeX e) a) b).symm

theorem context_no_marked : MarkedSubstitution.templateOccurrences 0 (contextTemplate L g h C)=0 := by
  unfold MarkedSubstitution.templateOccurrences
  have he : ((contextTemplate L g h C).vertices.filter (fun row => row.1==0))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro row hr
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hr
    simp [contextLabels]
  rw [he]
  rfl

abbrev templates : ℕ → Template := Adjoin.templates (L.count+1) (tagged L g).arity
  (contextTemplate L g h C)

theorem wellFormed : ∀i<L.count+2, (templates L g h C i).WellFormed
    (L.count+1) 1 (tagged L g).arity :=
  Adjoin.wellFormed _ (contextLabels L g h C).wellFormed

theorem template_marked (i : ℕ) (hi : i<L.count+2) :
    MarkedSubstitution.templateOccurrences 0 (templates L g h C i)=if i=0 then 1 else 0 := by
  by_cases ho : i<L.count+1
  · simp [templates,Adjoin.templates,ho,MarkedSubstitution.templateOccurrences,identityTemplate]
    by_cases hz : i=0 <;> simp [hz]
  · have he : i=L.count+1 := by omega
    rw [he]
    simpa [templates,Adjoin.templates] using context_no_marked L g h C

end
end Paper2.Paper1Proved.ReplicationTemplates
