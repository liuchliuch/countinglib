import Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessSemantics

/-! Source Lemma 2.10, effective clause. The actual finite controllers are
chosen before all valid finite layouts. Their optional output contains a
certified algebraic root and the literal matrix and inverse coordinates.
Every positive output is proved to satisfy the source class at that matrix. -/
namespace Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessRuntime
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Turing Computability
open Holant.Complexity.FixedFieldMachines
open Holant.Complexity.BinaryCompose
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open AlgebraicWitness (Class)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev Extra (C : Class) (d : Data) :=
  OriginalVariableLayout.Extra (OriginalAffineSystem.Entries d.arity) (parameterCount C d)
abbrev Candidate (C : Class) (d : Data) :=
  PositiveWitnessSearch.Candidate
    ((OriginalAffineSystem.Entries d.arity+2)+RationalInputSystem.count (typedBody C d))
    (Extra C d)

/-- The matrix decoded from precisely the returned coordinate vectors. -/
def decodedMatrix (C : Class) (d : Data) (theta : Paper2.Tractable.AlgebraicComplex)
    (a : Candidate C d) : Paper2.Kernel Paper2.Tractable.AlgebraicComplex :=
  fun u v => PowerArithmetic.decode theta (MatrixWitness.matrixCode a.1.2.2.2.2 u v)

def decodedInverse (C : Class) (d : Data) (theta : Paper2.Tractable.AlgebraicComplex)
    (a : Candidate C d) : Paper2.Kernel Paper2.Tractable.AlgebraicComplex :=
  fun u v => PowerArithmetic.decode theta
    (MatrixWitness.inverseCode a.1.2.1 a.1.2.2.2.2 u v)

/-- Positive output semantics preserve the exact emitted root, matrix and
inverse; the class witness is this matrix, shared by every table and the edge. -/
def ReturnedWitness (C : Class) (d : Data) (o : WitnessOutput.Output) : Prop :=
  ∃ a : Candidate C d, o = WitnessOutput.ofCandidate a ∧
    ∃ theta : Paper2.Tractable.AlgebraicComplex, o.root.Represents (theta : ℂ) ∧
      ∃ U : Paper2.Tractable.InvertibleKernel,
        U.matrix = decodedMatrix C d theta a ∧ U.inverse = decodedInverse C d theta a ∧
        (∀ i, AlgebraicWitness.Member C (U.symm.action (d.G i))) ∧
        AlgebraicWitness.Member C
          (Paper2.Tractable.kernelSignature (Paper2.Kernel.pullback d.E U.matrix))

private theorem coe_action {n : ℕ} (U : Paper2.Tractable.InvertibleKernel)
    (f : Paper2.Signature Paper2.Tractable.AlgebraicComplex n) :
    (fun x => (U.symm.action f x : ℂ)) =
      Signature.coordinateAction (fun _ a b => (U.inverse a b : ℂ))
        (fun x => (f x : ℂ)) := by
  funext x
  change (algebraMap Paper2.Tractable.AlgebraicComplex ℂ)
    (∑ y, (∏ j, U.inverse (x j) (y j)) * f y) = _
  simp only [map_sum,map_mul,map_prod]
  rfl

private theorem coe_edge (U : Paper2.Tractable.InvertibleKernel)
    (E : Paper2.Kernel Paper2.Tractable.AlgebraicComplex) :
    (fun x => (Paper2.Tractable.kernelSignature (Paper2.Kernel.pullback E U.matrix) x : ℂ)) =
      fun x : Fin 2 → Bool => Kernel.pullback (fun a b => (E a b : ℂ))
        (fun a b => (U.matrix a b : ℂ)) (x 0) (x 1) := by
  funext x
  change (algebraMap Paper2.Tractable.AlgebraicComplex ℂ)
    (Paper2.Kernel.pullback E U.matrix (x 0) (x 1)) = _
  simp only [Paper2.Kernel.pullback,Paper2.Kernel.mul,Paper2.Kernel.transpose,
    Kernel.pullback,Kernel.mul,Kernel.transpose,map_sum,map_mul]
  rfl

/-- Soundness of the literal returned matrix, without selecting another
algebraic point after deciding existence. -/
theorem returned_sound (C : Class) (d : Data) (o : WitnessOutput.Output)
    (ho : output C d = some o) : ReturnedWitness C d o := by
  obtain ⟨a,_,heo,theta,hr,hrel,hinv,hbind,heq⟩ := WitnessOutput.original_returned_sound
    (rootFn d) (valid d) (values d) (roots_represented d)
    (typedBody C d) (bindings C d) o ho
  let U : Paper2.Tractable.InvertibleKernel :=
    ⟨decodedMatrix C d theta a,decodedInverse C d theta a,hinv.1,hinv.2⟩
  let z : Fin (OriginalVariableLayout.Width (OriginalAffineSystem.Entries d.arity)
      (parameterCount C d)) → ℂ :=
    fun i => (PowerArithmetic.decode theta (a.1.2.2.2.2 i) : ℂ)
  have hm : matrixAt C d z = fun u v => (U.matrix u v : ℂ) := by
    funext u v
    rfl
  have hi : inverseAt C d z = fun u v => (U.inverse u v : ℂ) := by
    funext u v
    dsimp only [U,decodedInverse]
    rw [MatrixWitness.decode_inverse theta a.1.2.1 a.1.2.2.2.2 hrel]
    change inverseAt C d z u v =
      (algebraMap Paper2.Tractable.AlgebraicComplex ℂ)
        (SymbolicTransform.inverse (MatrixWitness.values theta a.1.2.2.2.2) u v)
    simp only [inverseAt,point,OriginalTensorRows.point,SymbolicTransform.inverse,
      SymbolicTransform.adjugate,SymbolicTransform.matrix,Sum.elim_inl,
      map_mul,MatrixWitness.values]
    split_ifs <;> simp only [map_neg,IntermediateField.algebraMap_apply] <;> rfl
  have hclasses := classes_of_zero C d z hbind heq
  rw [hm,hi] at hclasses
  have hG : ∀ i, AlgebraicWitness.ComplexMember C (fun x => (U.symm.action (d.G i) x : ℂ)) := by
    intro i
    rw [coe_action]
    exact hclasses.1 i
  have hE : AlgebraicWitness.ComplexMember C (fun x =>
      (Paper2.Tractable.kernelSignature (Paper2.Kernel.pullback d.E U.matrix) x : ℂ)) := by
    rw [coe_edge]
    exact hclasses.2
  have hc := AlgebraicWitness.witness_at_of_complex C d.G d.E U hG hE
  exact ⟨a,heo,theta,hr,U,rfl,rfl,hc.1,hc.2⟩

/-- Source 2.10's effectivity statement uses fixed physical programs across
all valid algebraic finite inputs. Recognition is effective; no uniform
polynomial bound for the varying signature language is asserted. -/
theorem theorem_2_10_effective :
    ∃ programs : Class → Machine,
      (∀ C d, ∃ ticks, Nonempty (TM2OutputsInTime (programs C).computer
        (encoding.encode (encode d))
        (some (WitnessOutput.resultEncoding.encode (output C d))) ticks)) ∧
      (∀ C d, (output C d).isSome = true ↔ AlgebraicWitness.ComplexWitness C d.G d.E) ∧
      (∀ C d o, output C d = some o → ReturnedWitness C d o) :=
  ⟨machine,source_outputs,accepts_iff,returned_sound⟩

end
end Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessRuntime

