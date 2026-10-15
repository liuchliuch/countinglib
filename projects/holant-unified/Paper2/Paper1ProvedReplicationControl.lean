import Paper2.Paper1ProvedReplicationGraphs

/-! The executed replication controller uses the copied-signature count to
cancel the fixed context scalar, then cancels the fixed nonzero closure value.
Every oracle query is the proved exactly-one graph, with a polynomial byte
bound on all executed prefixes. -/
namespace Paper2.Paper1Proved.ReplicationControl
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
open Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.LocalDrafts.Hardness
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}

 def correction (F : FixedField K d) (scale closure : K) :
     Computes (pairEncoding F.encoding GraphPreprocessing.UnaryBinary.unaryEncoding) F.encoding
       (fun p : K × ℕ => (p.1*(scale⁻¹)^p.2)*closure⁻¹) :=
   (pairComputes (ScalarPower.correction F scale)
     (constantComputes (pairEncoding F.encoding GraphPreprocessing.UnaryBinary.unaryEncoding)
       F.encoding closure⁻¹)).andThen (Concrete.fieldMultiplication F)

 def controlled (L : Language) {r s : ℕ} (g : Signature AlgebraicComplex r)
     (h : Signature AlgebraicComplex s) (C : CarrierContext L g h) (Z : NonzeroTaggedClosure L g)
     (F : FixedField K d) (scale closure : K) (hscale : scale≠0) (hclosure : closure≠0)
     (source : ReplicationCompiler.Input (ReplicationGraphs.data L g h Z) → K)
     (target : ReplicationGraphs.MarkedInput L g → K)
     (size : PolynomialOutputBound (ReplicationGraphs.markedEncoding L g) F.encoding target)
     (partition : ∀ x,target (ReplicationGraphs.query L g h C Z x)=
       scale^ReplicationCompiler.count x.val.vertices * closure * source x) :
     LengthControlledOracleReduction (ReplicationCompiler.inputEncoding (ReplicationGraphs.data L g h Z))
       F.encoding (ReplicationGraphs.markedEncoding L g) F.encoding source target := by
   let pre := pairComputes (ReplicationGraphs.queryComputes L g h C Z)
     (ReplicationCompiler.countComputes (ReplicationGraphs.data L g h Z))
   apply ControlledCap.controlledContextOfEq pre (correction F scale closure) size source
   intro x
   change source x=(target (ReplicationGraphs.query L g h C Z x)*
     (scale⁻¹)^ReplicationCompiler.count x.val.vertices)*closure⁻¹
   rw [partition,mul_assoc (scale^ReplicationCompiler.count x.val.vertices) closure (source x),
     ScalarPower.cancel_scale_power scale (closure*source x) hscale]
   rw [mul_right_comm, mul_inv_cancel₀ hclosure,one_mul]

 theorem reducesOfPartition (L : Language) {r s : ℕ} (g : Signature AlgebraicComplex r)
     (h : Signature AlgebraicComplex s) (C : CarrierContext L g h) (Z : NonzeroTaggedClosure L g)
     (F : FixedField K d) (embed : K →ₗ[ℚ] AlgebraicComplex) (injective : Function.Injective embed)
     (scale closure : K) (hscale : scale≠0) (hclosure : closure≠0)
     (source : ReplicationCompiler.Input (ReplicationGraphs.data L g h Z) → K)
     (target : ReplicationGraphs.MarkedInput L g → K)
     (size : PolynomialOutputBound (ReplicationGraphs.markedEncoding L g) F.encoding target)
     (sourceCorrect : ∀ G,embed (source (ReplicationGraphs.sourceInput L g h Z G))=
       Problem.value .nativeX (tagged L h) G)
     (targetCorrect : ∀ G,embed (target G)=Problem.value .nativeX (tagged L g)
       (ReplicationGraphs.canonicalTargetInput L g G).val)
     (partition : ∀ x,target (ReplicationGraphs.query L g h C Z x)=
       scale^ReplicationCompiler.count x.val.vertices * closure * source x)
     (one : FixedFieldOutput.TaggedReduces .nativeX L g (fun k => k=1) L) :
     FixedFieldOutput.Reduces .nativeX (tagged L h) L := by
   let old := controlled L g h C Z F scale closure hscale hclosure source target size partition
   let first := canonicalPromisedReduction (tagged L h) L g
     (ReplicationCompiler.inputEncoding (ReplicationGraphs.data L g h Z))
     (ReplicationGraphs.markedEncoding L g) F embed injective source target
     (ReplicationGraphs.sourceInput L g h Z) (ReplicationGraphs.sourceComputes L g h Z)
     sourceCorrect (ReplicationGraphs.canonicalTargetInput L g)
     (ReplicationGraphs.canonicalTargetComputes L g) targetCorrect old
   obtain ⟨last⟩ := one
   exact ⟨first.controlledCompose last⟩


end
end Paper2.Paper1Proved.ReplicationControl
