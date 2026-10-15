import Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessRuntime

/-! Actual terminating witness runs on certified arbitrary-edge descriptors.
The physical controller sees only the varying table layout and original root
bytes. Algebraic values and validity proofs occur only in the source theorem. -/
namespace Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessRuntime
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open AlgebraicWitness (Class)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

structure Data where
  count : ℕ
  arity : Fin count → ℕ
  G : (i : Fin count) → Paper2.Signature Paper2.Tractable.AlgebraicComplex (arity i)
  E : Paper2.Kernel Paper2.Tractable.AlgebraicComplex
  input : (i : Fin count) → (Fin (arity i) → Bool) → RootCode
  edge : Bool → Bool → RootCode
  represented : ∀ i x, (input i x).Represents (G i x : ℂ)
  edgeRepresented : ∀ a b, (edge a b).Represents (E a b : ℂ)

def encode (d : Data) : Input :=
  (OriginalFamilyPackingSource.fromSource d.arity d.input false,
    (SparseTransform.allWords 2).map (fun x => d.edge (x 0) (x 1)))

def rootFn (d : Data) := OriginalVariableLayout.descriptors
  (AlgebraicWitness.input d.arity d.input d.edge)
def values (d : Data) := OriginalAffineDecision.originalValues d.arity
  (AlgebraicWitness.values d.arity d.G d.E)

theorem roots_represented (d : Data) : ∀ i, (rootFn d i).Represents (values d i : ℂ) := by
  intro i
  change (rootFn d i).Represents
    (OriginalAffineDecision.originalValues d.arity (AlgebraicWitness.values d.arity d.G d.E) i : ℂ)
  rw [congrFun (OriginalAffineDecision.originalValues_coe d.arity _) i]
  exact OriginalVariableLayout.descriptors_represents _ _
    (AlgebraicWitness.input_represents d.arity d.G d.E d.input d.edge
      d.represented d.edgeRepresented) i

theorem valid (d : Data) : OriginalSystemDecision.Valid (rootFn d) :=
  ⟨values d, roots_represented d⟩

theorem roots_encode (d : Data) : roots (encode d) = List.ofFn (rootFn d) := by
  have hpack : List.ofFn (AlgebraicWitness.input d.arity d.input d.edge) =
      (LocalAffineVariableLayout.catalogue d.arity).map
        (fun p => match p with
          | ⟨.inl i,x⟩ => d.input i x
          | ⟨.inr _,x⟩ => d.edge (x (0 : Fin 2)) (x (1 : Fin 2))) := by
    rw [← List.ofFn_get (LocalAffineVariableLayout.catalogue d.arity), List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply]
    unfold AlgebraicWitness.input
    generalize (LocalAffineVariableLayout.catalogue d.arity).get i = p
    rcases p with ⟨j,x⟩
    cases j <;> rfl
  change roots (encode d) = List.ofFn
    (Fin.addCases (AlgebraicWitness.input d.arity d.input d.edge) StandardRootCodes.descriptors)
  rw [OriginalFamilyPackingSource.ofFn_addCases,hpack]
  simp only [roots,encode,OriginalFamilyPackingSource.fromSource,
    LocalAffineVariableLayout.catalogue,ProductVariableLayout.slots,
    List.flatMap_map,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.map_flatMap,List.map_map,List.map_append,Function.comp_def]
  rfl

def parameterCount (C : Class) (d : Data) : ℕ :=
  match C with
  | .affine => d.count+1
  | .product => OriginalProductSystem.Count d.arity
  | .localAffine => OriginalLocalAffineSystem.Count d.arity

def typedBody (C : Class) (d : Data) :
    List (Sparse.Poly (OriginalVariableLayout.Width
      (OriginalAffineSystem.Entries d.arity) (parameterCount C d)) 1) :=
  match C with
  | .affine => RawAffineRecognitionSource.combined d.arity d.input
  | .product => RawProductRecognitionSource.combined d.arity d.input
  | .localAffine => RawLocalAffineRecognitionSource.combined d.arity d.input

def bindings (C : Class) (d : Data) := OriginalVariableLayout.binding
  (OriginalAffineSystem.Entries d.arity) (parameterCount C d)

theorem request_encode (C : Class) (d : Data) :
    request C (encode d) = RationalInputMachine.fromSource
      (rootFn d) (typedBody C d) (bindings C d) := by
  cases C with
  | affine =>
    simp only [request,width,body,addresses,encode,typedBody,bindings,parameterCount,
      OriginalFamilyPackingSource.width_exact,OriginalFamilyPackingSource.addresses_exact,
      RawAffineRecognitionSource.body_wire,RationalInputMachine.fromSource]
    rw [←roots_encode]
    rfl
  | product =>
    simp only [request,width,body,addresses,encode,typedBody,bindings,parameterCount,
      RawProductRecognitionMachine.allocated,ProductAllocationSource.count_source,
      OriginalAllocatedPackingMachine.width_source,OriginalAllocatedPackingMachine.addresses_source,
      RawProductRecognitionSource.body_wire,RationalInputMachine.fromSource]
    rw [←roots_encode]
    rfl
  | localAffine =>
    simp only [request,width,body,addresses,encode,typedBody,bindings,parameterCount,
      RawLocalAffineRecognitionMachine.allocated,LocalAffineAllocationSource.count_raw,
      OriginalAllocatedPackingMachine.width_source,OriginalAllocatedPackingMachine.addresses_source,
      RawLocalAffineRecognitionSource.body_wire,RationalInputMachine.fromSource]
    rw [←roots_encode]
    rfl

def output (C : Class) (d : Data) : Option WitnessOutput.Output :=
  WitnessOutput.originalOutput (rootFn d) (valid d) (typedBody C d) (bindings C d)

/-- The actual witness-returning controller terminates for each valid input,
including singular edges, zero tables, nullary rows and an empty family. -/
theorem source_outputs (C : Class) (d : Data) :
    ∃ ticks, Nonempty (TM2OutputsInTime (machine C).computer
      (encoding.encode (encode d)) (some (WitnessOutput.resultEncoding.encode (output C d))) ticks) := by
  obtain ⟨ticks,⟨run⟩⟩ := WitnessOutput.original_outputs
    (rootFn d) (valid d) (typedBody C d) (bindings C d)
  have prepared := (requestExecutes C).outputs (encode d)
  rw [request_encode] at prepared
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ prepared run⟩⟩

def runs (C : Class) : Holant.LocalDrafts.RemoteWork.TractChainV1.PhysicalFolds.Runs
    encoding WitnessOutput.resultEncoding encode (output C) where
  machine := machine C
  cost d := Classical.choose (source_outputs C d)
  outputs d := Classical.choice (Classical.choose_spec (source_outputs C d))

theorem guard_mem (C : Class) (d : Data) :
    SparseTransform.guard RationalCompiler.data
      (OriginalVariableLayout.Extra (OriginalAffineSystem.Entries d.arity) (parameterCount C d)) ∈
        typedBody C d := by
  cases C <;> exact List.mem_cons_self ..

/-- A positive returned packet is equivalent to a solution of the exact
original bindings and rational body. The supplied edge remains arbitrary. -/
theorem output_correct (C : Class) (d : Data) :
    (output C d).isSome = true ↔
      ∃ z : Fin (OriginalVariableLayout.Width (OriginalAffineSystem.Entries d.arity)
        (parameterCount C d)) → ℂ,
        (∀ i, z (bindings C d i) = (values d i : ℂ)) ∧
        ∀ p ∈ typedBody C d,
          SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p = 0 := by
  rw [output,WitnessOutput.originalOutput_correct _ _ (values d) (roots_represented d)
    _ _ (guard_mem C d)]
  exact exists_congr (fun z => RationalInputSystem.system_zero_iff _ _ _ z)

end
end Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessRuntime
