import Paper2.Paper1ProvedReplicationTemplates

/-! The literal nonzero closure selects its unique designated carrier row.
The emitted chain and context substitution are real finite Boolean programs;
validation and the exactly-one promise add no graph bytes. -/
namespace Paper2.Paper1Proved.ReplicationGraphs
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
open Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable (L : Language) {r s : ℕ}
variable (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s)
variable (C : CarrierContext L g h) (Z : NonzeroTaggedClosure L g)

abbrev oldClosure := input (tagged L g) Z.closedInput.val
 theorem oldClosure_count : ReplicationCompiler.count (oldClosure L g Z).val.vertices=1 := Z.closedInput.property
 def seedIndex : Fin (oldClosure L g Z).val.vertices.length :=
  Classical.choose (ReplicationCompiler.unique_seed _ (oldClosure_count L g Z))
 theorem seed_label : ((oldClosure L g Z).val.vertices.get (seedIndex L g Z)).1=0 :=
  (Classical.choose_spec (ReplicationCompiler.unique_seed _ (oldClosure_count L g Z))).1
 theorem seed_selected : RawGrouping.selected 0 (oldClosure L g Z).val.vertices=
     ((oldClosure L g Z).val.vertices.get (seedIndex L g Z)).2 :=
  (Classical.choose_spec (ReplicationCompiler.unique_seed _ (oldClosure_count L g Z))).2

 def data (L : Language) {r s : ℕ} (g : Signature AlgebraicComplex r)
     (h : Signature AlgebraicComplex s) (Z : NonzeroTaggedClosure L g) : ReplicationCompiler.Data :=
  ⟨L.count,r,s,L.arity,(oldClosure L g Z).val,(seedIndex L g Z).val⟩
 theorem sourceArity : (data L g h Z).sourceArity=(tagged L h).arity := by
  funext i
  exact (ReplicationTemplates.tagged_arity L h i).symm
 theorem carrierArity : (data L g h Z).carrierArity=(tagged L g).arity := by
  funext i
  exact (ReplicationTemplates.tagged_arity L g i).symm
 theorem closure_valid : (data L g h Z).closure.WellFormed (L.count+1) 1
     (data L g h Z).carrierArity := by
  rw [carrierArity]
  exact (oldClosure L g Z).property
 theorem closure_count : ReplicationCompiler.count (data L g h Z).closure.vertices=1 := oldClosure_count L g Z
 theorem closure_selected : RawGrouping.selected 0 (data L g h Z).closure.vertices=
     (data L g h Z).seedPorts := by
  rw [show (data L g h Z).seedPorts=((oldClosure L g Z).val.vertices.get (seedIndex L g Z)).2 from by
    simp [ReplicationCompiler.Data.seedPorts,data,List.get_eq_getElem]]
  exact seed_selected L g Z
 theorem seed_length : (data L g h Z).seedPorts.length=r := by
  have hh := ((oldClosure L g Z).property.1 (seedIndex L g Z)).2
  rw [seed_label,tagged_arity_zero] at hh
  simpa [ReplicationCompiler.Data.seedPorts,data,List.get_eq_getElem] using hh

 def sourceInput (G : Instance (tagged L h)) : ReplicationCompiler.Input (data L g h Z) :=
  ⟨(input (tagged L h) G).val,by rw [sourceArity]; exact G.property⟩
 def sourceComputes : Paper2.Complexity.BinaryCompose.Computes (inputEncoding (tagged L h))
     (ReplicationCompiler.inputEncoding (data L g h Z)) (sourceInput L g h Z) :=
  Paper2.Complexity.FixedFieldMachines.recode
    (Paper2.Complexity.BinaryCompose.identityComputes (inputEncoding (tagged L h)))
    id (fun _ => rfl) (fun G => (input_bytes (tagged L h) G).symm)

 theorem boundary (i : ℕ) (hi : i<L.count+2) :
     FixedGadgetSubstitution.sourceArity (ReplicationTemplates.templates L g h C) i=(data L g h Z).targetArity i := by
  by_cases ho : i<L.count+1
  · have hn : i≠L.count+1 := by omega
    change (ReplicationTemplates.templates L g h C i).boundary=_
    simp only [ReplicationTemplates.templates,Adjoin.templates,if_pos ho,identityTemplate]
    rw [ReplicationCompiler.Data.targetArity]
    simp only [data,if_neg hn]
    exact congrFun (carrierArity L g h Z).symm i
  · have he : i=L.count+1 := by omega
    subst i
    simp [ReplicationTemplates.templates,Adjoin.new_boundary,data,ReplicationCompiler.Data.targetArity]


 abbrev ChainInput := ExactSignatureTables.Input (L.count+2) 1
   (FixedGadgetSubstitution.sourceArity (ReplicationTemplates.templates L g h C))
 def chainInput (x : ReplicationCompiler.Input (data L g h Z)) : ChainInput L g h C :=
  ⟨ReplicationCompiler.query (data L g h Z) x,by
    have hw := ReplicationCompiler.query_valid (data L g h Z) x (closure_valid L g h Z)
      (closure_count L g h Z) (closure_selected L g h Z) (seed_length L g h Z)
    refine ⟨?_,hw.2⟩
    intro v
    exact ⟨(hw.1 v).1,by rw [boundary L g h C Z _ (hw.1 v).1]; exact (hw.1 v).2⟩⟩
 def chainComputes : Computes (ReplicationCompiler.inputEncoding (data L g h Z))
     (RawClosedNetwork.validatedEncoding (L.count+2) 1
       (FixedGadgetSubstitution.sourceArity (ReplicationTemplates.templates L g h C))) (chainInput L g h C Z) :=
   recode (ReplicationCompiler.rawComputes (data L g h Z)) id (fun _ => rfl) (fun _ => rfl)

 abbrev MarkedInput := {G : SourceInput (tagged L g) // FixedGadgetSubstitution.occurrences 0 G.val=1}
 def markedEncoding : Encoding (MarkedInput L g) Bool where
   encode G := (sourceEncoding (tagged L g)).encode G.val
   decode bits := ((sourceEncoding (tagged L g)).decode bits).bind (fun G =>
     if h : FixedGadgetSubstitution.occurrences 0 G.val=1 then some ⟨G,h⟩ else none)
   decode_encode G := by simp [G.property]

 def query (x : ReplicationCompiler.Input (data L g h Z)) : MarkedInput L g := by
   let p := Compiler.value (L.count+2) 1
     (FixedGadgetSubstitution.sourceArity (ReplicationTemplates.templates L g h C))
     (ReplicationTemplates.templates L g h C) (L.count+1) (tagged L g).arity
     (compilerHypotheses _ (ReplicationTemplates.wellFormed L g h C)) (chainInput L g h C Z x)
   refine ⟨p,?_⟩
   have hc := ReplicationCompiler.query_one_marked (data L g h Z) x (closure_count L g h Z)
   have hp := MarkedSubstitution.preserves (ReplicationTemplates.templates L g h C)
     (ReplicationCompiler.query (data L g h Z) x) (fun row hr =>
       ReplicationTemplates.template_marked L g h C row.1
         (((RawGrouping.wellFormed_iff_members _ _ _ _).mp
           (chainInput L g h C Z x).property).1 row hr).1)
   exact hp.trans hc

 def queryComputes : Computes (ReplicationCompiler.inputEncoding (data L g h Z)) (markedEncoding L g)
     (query L g h C Z) :=
   recode ((chainComputes L g h C Z).andThen
     (Compiler.computes (L.count+2) 1
       (FixedGadgetSubstitution.sourceArity (ReplicationTemplates.templates L g h C)) (ReplicationTemplates.templates L g h C)
       (L.count+1) (tagged L g).arity (compilerHypotheses _ (ReplicationTemplates.wellFormed L g h C))))
       id (fun _ => rfl) (fun _ => rfl)

 def canonicalTargetInput (G : MarkedInput L g) : TaggedInstance L g (fun k => k=1) :=
   ⟨(inputIso (tagged L g)).symm G.val,G.property⟩
 def canonicalTargetComputes : Paper2.Complexity.BinaryCompose.Computes (markedEncoding L g)
     (taggedEncoding L g (fun k => k=1)) (canonicalTargetInput L g) :=
   Paper2.Complexity.FixedFieldMachines.recode
     (Paper2.Complexity.BinaryCompose.identityComputes (markedEncoding L g)) id
       (fun _ => rfl) (fun G => input_bytes_back (tagged L g) G.val)

end
end Paper2.Paper1Proved.ReplicationGraphs
