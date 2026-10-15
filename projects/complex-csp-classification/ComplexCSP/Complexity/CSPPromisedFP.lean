import ComplexCSP.Complexity.CSPCountReduction
import ComplexCSP.Complexity.GadgetSubstitutionReduction
import PlanarHom.PromisePolynomialTime

/-! # Honest canonical-word interfaces for actual CSP evaluators

A total typed evaluator need agree only on the actual source promise. The raw
input is already exactly its canonical codeword, so this transfer is reuse of
the same bit machine, with no hidden parser, promise decider or normalization.
-/
noncomputable section
namespace ComplexCSP.ComplexityCSPPromisedFP
open PlanarHom PlanarHom.Complexity ComplexityCSPCode
variable {D K : Type} [Fintype D] [Field K] [DecidableEq K] [Algebra ℚ K]
variable {s dimension : ℕ} (L : Language D K (Fin s))
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- General canonical-promise transfer retains every byte of the original input. -/
theorem canonical_inFP {A B : Type} (ea : BitEncoding A) (eb : BitEncoding B)
    (promise : A → Prop) (f run : A → B) (default : Bits)
    (hrun : FP ea eb run) (hcorrect : ∀ a, promise a → run a=f a) :
    (⟨fun raw => ∃ a, promise a ∧ ea.encode a=raw,
      encodedFunction ea eb f default⟩ : PromiseProblem).InFP := by
  classical
  let P : PromiseProblem := ⟨fun raw => ∃ a, promise a ∧ ea.encode a=raw,
    encodedFunction ea eb f default⟩
  let value : {raw : Bits // P.valid raw} → A := fun raw => raw.property.choose
  have hv : ∀ raw : {raw : Bits // P.valid raw}, ea.encode (value raw)=raw.val :=
    fun raw => raw.property.choose_spec.2
  have hp : ∀ raw : {raw : Bits // P.valid raw}, promise (value raw) :=
    fun raw => raw.property.choose_spec.1
  have h := hrun.transportInput (ea:=BitEncoding.bits.restrict P.valid) value (fun raw => hv raw)
  apply h.transportOutput
  intro raw
  change eb.encode (run (value raw)) = encodedFunction ea eb f default raw.val
  rw [hcorrect _ (hp raw),←hv raw,encodedFunction_encode]

omit [DecidableEq K] in
/-- Ordinary partition on exactly the declared canonical valid-code promise. -/
theorem partition_inFP (run : Code → K) (hrun : FP encoding (numberFieldEncoding basis) run)
    (hcorrect : ∀ g, Valid L g → run g=partition L g) :
    (ComplexityCSPCountReduction.partitionProblem L basis).InFP :=
  canonical_inFP encoding (numberFieldEncoding basis) (Valid L) (partition L) run [] hrun hcorrect

omit [DecidableEq K] in
/-- The degree branch assumes correctness only on actual divisible instances;
ordinary or malformed inputs are not smuggled into its semantic hypothesis. -/
theorem degreePartition_inFP (δ : ℕ) (run : Code → K)
    (hrun : FP encoding (numberFieldEncoding basis) run)
    (hcorrect : ∀ g, ComplexityGadgetSubstitution.DegreeValid L δ g → run g=partition L g) :
    (ComplexityGadgetSubstitution.degreePartitionProblem L basis δ).InFP :=
  canonical_inFP encoding (numberFieldEncoding basis) (ComplexityGadgetSubstitution.DegreeValid L δ)
    (partition L) run [] hrun hcorrect

end ComplexCSP.ComplexityCSPPromisedFP
