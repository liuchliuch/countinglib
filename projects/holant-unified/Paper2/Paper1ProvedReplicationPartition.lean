import Paper2.Paper1ProvedReplicationGraphs
import Paper2.Paper1ProvedReplicationSemantics

/-! Exact algebraic partition of the physically substituted copying chain.
The native context and original-family macro labels identify the literal table;
all source signature occurrences and the fixed closure remain in the product. -/
namespace Paper2.Paper1Proved.ReplicationPartition
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
open Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
variable (L : Language) {r s : ℕ}
variable (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s)
variable (C : CarrierContext L g h) (Z : NonzeroTaggedClosure L g)

 theorem tagged_table_zero (bits : List Bool) :
     Choice.table (signatures (tagged L g)) 0 bits=g (ReplicationSemantics.word r bits) := by
   have he := congrArg (fun f : AnySignature AlgebraicComplex =>
     f.2 (fun i => bits.getD i.val false)) (tagged_zero L g)
   rw [Choice.table,dif_pos (show 0<(tagged L g).count by simp)]
   exact he

 theorem tagged_table_succ (i : ℕ) (bits : List Bool) :
     Choice.table (signatures (tagged L g)) (i+1) bits=Choice.table (signatures L) i bits := by
   by_cases hi : i<L.count
   · have he := congrArg (fun f : AnySignature AlgebraicComplex =>
       f.2 (fun j => bits.getD j.val false)) (tagged_succ L g ⟨i,hi⟩)
     simpa [Choice.table,signatures,hi,show i+1<L.count+1 by omega] using he
   · simp [Choice.table,hi,show ¬ i+1<L.count+1 by omega]

 theorem marked_g_table :
     ReplicationSemantics.markedTable (Choice.table (signatures (tagged L g))) g=
       Choice.table (signatures (tagged L g)) := by
   funext label bits
   by_cases hz : label=0
   · simpa [ReplicationSemantics.markedTable,hz] using (tagged_table_zero L g bits).symm
   · simp [ReplicationSemantics.markedTable,hz]

 theorem marked_h_table :
     ReplicationSemantics.markedTable (Choice.table (signatures (tagged L g))) h=
       Choice.table (signatures (tagged L h)) := by
   funext label bits
   cases label with
   | zero => simpa [ReplicationSemantics.markedTable] using (tagged_table_zero L h bits).symm
   | succ i => simp [ReplicationSemantics.markedTable,tagged_table_succ]

 def macros (i : Fin (L.count+2)) : Holant.Signature AlgebraicComplex
     (FixedGadgetSubstitution.sourceArity (ReplicationTemplates.templates L g h C) i.val) :=
   ((ReplicationTemplates.templates L g h C i.val).network
     (ReplicationTemplates.wellFormed L g h C i.val i.isLt)
     (signatures (tagged L g)) (kernels .nativeX)).denote

 theorem old_macro (i : Fin (L.count+1)) :
     (⟨FixedGadgetSubstitution.sourceArity (ReplicationTemplates.templates L g h C) i.val,
       macros L g h C ⟨i.val,by omega⟩⟩ : AnySignature AlgebraicComplex)=
         ⟨(tagged L g).arity i.val,(tagged L g).signature i⟩ := by
   have ht : ReplicationTemplates.templates L g h C i.val=identityTemplate (tagged L g).arity i.val := by
     simp [ReplicationTemplates.templates,Adjoin.templates,i.isLt]
   have he := GadgetProvider.templateDenote_congr (tagged L g) _ _ ht
     (ReplicationTemplates.wellFormed L g h C i.val (by omega))
     (identityTemplate_wellFormed (tagged L g).arity i)
   have hd := identityTemplate_denote (tagged L g).arity i
     (signatures (tagged L g)) (kernels .nativeX)
   exact Sigma.ext (by simp [FixedGadgetSubstitution.sourceArity,ht,identityTemplate])
     (he.trans (heq_of_eq hd))

 theorem new_macro :
     (⟨FixedGadgetSubstitution.sourceArity (ReplicationTemplates.templates L g h C) (L.count+1),
       macros L g h C ⟨L.count+1,by omega⟩⟩ : AnySignature AlgebraicComplex)=
         ⟨r+(r+s),C.graph.denote⟩ := by
   have ht : ReplicationTemplates.templates L g h C (L.count+1)=
       ReplicationTemplates.contextTemplate L g h C := by
     simp [ReplicationTemplates.templates,Adjoin.templates]
   have he := GadgetProvider.templateDenote_congr (tagged L g) _ _ ht
     (ReplicationTemplates.wellFormed L g h C (L.count+1) (by omega))
     (ReplicationTemplates.contextLabels L g h C).wellFormed
   exact Sigma.ext (by simp [FixedGadgetSubstitution.sourceArity,ht])
     (he.trans (heq_of_eq (ReplicationTemplates.contextDenote L g h C)))

 theorem macro_table : Choice.table (macros L g h C)=
     ReplicationSemantics.targetTable (L.count+1)
       (Choice.table (signatures (tagged L g))) g (ReplicationSemantics.contextTable C) := by
   funext label bits
   by_cases ho : label<L.count+1
   · have hi : label<L.count+2 := by omega
     have hn : label≠L.count+1 := by omega
     have he := congrArg (fun f : AnySignature AlgebraicComplex =>
       f.2 (fun i => bits.getD i.val false)) (old_macro L g h C ⟨label,ho⟩)
     rw [ReplicationSemantics.targetTable,if_neg hn,marked_g_table L g]
     simpa only [Choice.table,tagged_count,dif_pos hi,dif_pos ho] using he
   · by_cases hn : label=L.count+1
     · subst label
       have he := congrArg (fun f : AnySignature AlgebraicComplex =>
         f.2 (fun i => bits.getD i.val false)) (new_macro L g h C)
       rw [Choice.table]
       simp only [show L.count+1<L.count+2 by omega,↓reduceDIte]
       rw [ReplicationSemantics.targetTable]
       simp only [↓reduceIte]
       rw [show ReplicationSemantics.contextTable C=
         (fun a p y => C.graph.denote (Fin.append a (Fin.append p y))) from rfl,
         ReplicationSemantics.contextWord_signature]
       exact he
     · have hi : ¬ label<L.count+2 := by omega
       have hz : label≠0 := by omega
       simp [Choice.table,hi,ho,ReplicationSemantics.targetTable,hn,
         ReplicationSemantics.markedTable,hz]

 def sourceOriginal (x : ReplicationCompiler.Input (ReplicationGraphs.data L g h Z)) :
     SourceInput (tagged L h) :=
   ⟨x.val,by rw [← ReplicationGraphs.sourceArity L g h Z]; exact x.property⟩

 theorem physical_partition (x : ReplicationCompiler.Input (ReplicationGraphs.data L g h Z)) :
     (((ReplicationGraphs.query L g h C Z x).val.val).realize
       (ReplicationGraphs.query L g h C Z x).val.property
       (signatures (tagged L g)) (kernels .nativeX)).denote Fin.elim0 =
       C.scalar^ReplicationCompiler.count x.val.vertices *
       (((ReplicationGraphs.oldClosure L g Z).val).realize
         (ReplicationGraphs.oldClosure L g Z).property
         (signatures (tagged L g)) (kernels .nativeX)).denote Fin.elim0 *
       (((sourceOriginal L g h Z x).val).realize (sourceOriginal L g h Z x).property
         (signatures (tagged L h)) (kernels .nativeX)).denote Fin.elim0 := by
   let d := ReplicationGraphs.data L g h Z
   let chain := ReplicationGraphs.chainInput L g h C Z x
   have hp := replacement_partition (ReplicationTemplates.templates L g h C) chain.val chain.property
     (ReplicationTemplates.wellFormed L g h C) (macros L g h C)
     (signatures (tagged L g)) (kernels .nativeX) (fun _ => (1 : AlgebraicComplex))
     (fun i => by simp [macros])
   have hreplace :
       (((ReplicationGraphs.query L g h C Z x).val.val).realize
         (ReplicationGraphs.query L g h C Z x).val.property
         (signatures (tagged L g)) (kernels .nativeX)).denote Fin.elim0 =
       (chain.val.realize chain.property (macros L g h C) (kernels .nativeX)).denote Fin.elim0 := by
     simpa only [Finset.prod_const_one,one_mul] using hp
   rw [hreplace]
   have hk : Paper2.Paper1Proved.kernels .nativeX=
     (fun _ : Fin 1 => Holant.Signature.disequality) := rfl
   simp only [hk,Choice.denote_eq_evaluate]
   rw [macro_table]
   have hc := ReplicationSemantics.context_query_partition d x L
     (Choice.table (signatures (tagged L g))) g h C
     (ReplicationGraphs.closure_valid L g h Z) (ReplicationGraphs.closure_count L g h Z)
     (ReplicationGraphs.closure_selected L g h Z) (ReplicationGraphs.seed_length L g h Z)
   change Choice.evaluate (ReplicationSemantics.targetTable (L.count+1)
     (Choice.table (signatures (tagged L g))) g (ReplicationSemantics.contextTable C))
     (ReplicationCompiler.query d x).edges.length (ReplicationCompiler.query d x).vertices = _ at hc
   change Choice.evaluate (ReplicationSemantics.targetTable (L.count+1)
     (Choice.table (signatures (tagged L g))) g (ReplicationSemantics.contextTable C))
     (ReplicationCompiler.query d x).edges.length (ReplicationCompiler.query d x).vertices = _
   rw [hc,marked_g_table L g,marked_h_table L g h]
   rfl


end
end Paper2.Paper1Proved.ReplicationPartition
