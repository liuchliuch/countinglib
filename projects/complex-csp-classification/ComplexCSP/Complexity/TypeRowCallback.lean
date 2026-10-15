import ComplexCSP.Complexity.WeightedLayers
import ComplexCSP.Structure.WeightedMaltsevMachineBridge
import ComplexCSP.Complexity.CSPMarginalRowBounds

/-! # Actual ComputeF/normalization callback for type search

The original CSP instance and all previously computed layers are immutable
ordinary input data. This callback has a concrete FP machine: no variable-arity
evaluator, row oracle, or serialized function closure is supplied.
-/
namespace ComplexCSP.ComplexityTypeRowCallback
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding
open ComplexityCSPCode ComplexityRowNormalization WeightedMaltsev
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d)

abbrev Context (K : Type) := Code × List (ComplexityWeightedLayers.Layer K)
noncomputable def contextCode : BitEncoding (Context K) :=
  encoding.prod (ComplexityWeightedLayers.layerCode basis).list

def evaluate (context : Context K) (word : List ℕ) : K :=
  ComplexityWeightedLayers.execute m L context.1 word context.2

def row (context : Context K) (word : List ℕ) : Fin d → K :=
  fun a => evaluate L m context (word ++ [a.val])

def label (context : Context K) (word : List ℕ) : RowLabel K d :=
  materializeLabel (normalize (row L m context word))

/-- Each of the fixed d row coordinates is a genuine ComputeF invocation. -/
theorem fp_row :
    FP ((contextCode basis).prod wordCode) (rowEncoding basis d)
      (fun p => row L m p.1 p.2) := by
  have hc := fp_fst (contextCode basis) wordCode
  have hw := fp_snd (contextCode basis) wordCode
  have hg := hc.comp (fp_fst encoding (ComplexityWeightedLayers.layerCode basis).list)
  have hl := hc.comp (fp_snd encoding (ComplexityWeightedLayers.layerCode basis).list)
  apply FixedVectorMachines.fp_assemble _ (numberFieldEncoding basis) d
  intro a
  have hx := (hw.pair (fp_const _ wordCode [a.val])).comp
    (ListMutationMachines.fp_append BitEncoding.nat)
  exact (hg.pair (hx.pair hl)).comp (ComplexityWeightedLayers.fp_execute basis m L)

theorem fp_materializeLabel :
    FP (resultEncoding basis d) (ComplexityCSPMarginalRowBounds.labelEncoding basis d)
      (materializeLabel : Result K d → RowLabel K d) := by
  apply fp_code_view
  intro r
  simp only [ComplexityCSPMarginalRowBounds.labelEncoding, BitEncoding.retract, decode_materialize]

theorem fp_label :
    FP ((contextCode basis).prod wordCode) (ComplexityCSPMarginalRowBounds.labelEncoding basis d)
      (fun p => label L m p.1 p.2) :=
  ((fp_row L basis m).comp (fp_normalize basis)).comp (fp_materializeLabel basis)

/-- Exact callback identity used when the continuation stack processes typed
prefix tuples; all later marginal data remain literal context fields. -/
theorem label_tuple {n : ℕ} (context : Context K) (x : MaltsevWitness.Tuple (Fin d) n) :
    label L m context (word x) =
      rowLabel (fun y => evaluate L m context (word y)) x := by
  unfold label rowLabel normalizedRow row
  congr 2
  funext a
  simp [word_snocTuple, MaltsevWitness.view_ofFn]

end ComplexCSP.ComplexityTypeRowCallback
