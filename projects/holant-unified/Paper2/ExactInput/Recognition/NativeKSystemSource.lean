import Paper2.ExactInput.Recognition.NativeKSystem
import Paper2.ExactInput.Recognition.NativeKSystemLayout
import Holant.Proofs.Recognition.RuntimeSupportTable

namespace Paper2.ExactInput.Recognition.NativeKSystem
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.RemoteWork.TractChainV1
open PhysicalFolds
open NativeKSystemLayout
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev coefficientCount (d : RuntimeSupportTable.Data) := (coefficientCatalogue d.arity).length
structure Data where
  source : RuntimeSupportTable.Data
  target : Fin (coefficientCount source) → RootCode
  value : Fin (coefficientCount source) → AlgebraicComplex
  represented : ∀j,(target j).Represents (value j : ℂ)

def encode (d : Data) : Input := (RuntimeSupportTable.original d.source,List.ofFn d.target)
abbrev RootCount (d : Data) := UniformKPolynomial.Count d.source.arity+coefficientCount d.source
abbrev Width (d : Data) := 5+RootCount d

def rootFn (d : Data) : Fin (RootCount d) → RootCode :=
  Fin.addCases (UniformKPolynomial.descriptors d.source.arity d.source.input) d.target
 def values (d : Data) : Fin (RootCount d) → AlgebraicComplex :=
  Fin.addCases (UniformKPolynomial.values d.source.arity d.source.G) d.value
 def bindings (d : Data) (j : Fin (RootCount d)) : Fin (Width d) := Fin.natAdd 5 j
 def oldIndex (d : Data) (p : LocalAffineVariableLayout.Parameters d.source.arity) : Fin (RootCount d) :=
  Fin.castAdd (coefficientCount d.source) (Fin.castAdd 2 (LocalAffineVariableLayout.address d.source.arity p))
 def sourceEntry (d : Data) (j : ProductVariableLayout.Slot d.source.count)
    (x : Fin (ProductVariableLayout.slotArity d.source.arity j) → Bool) : Fin (Width d) :=
  bindings d (oldIndex d ⟨j,x⟩)
 def imaginaryIndex (d : Data) : Fin (RootCount d) :=
  Fin.castAdd (coefficientCount d.source) (Fin.natAdd (OriginalAffineSystem.Entries d.source.arity) (0 : Fin 2))
 def sqrtIndex (d : Data) : Fin (RootCount d) :=
  Fin.castAdd (coefficientCount d.source) (Fin.natAdd (OriginalAffineSystem.Entries d.source.arity) (1 : Fin 2))
 def imaginaryEntry (d : Data) := bindings d (imaginaryIndex d)
 def sqrtEntry (d : Data) := bindings d (sqrtIndex d)
 def targetEntry (d : Data) (p : LocalAffineVariableLayout.Parameters d.source.arity) : Fin (Width d) :=
  if h : (LocalAffineVariableLayout.address d.source.arity p).val < coefficientCount d.source then
    bindings d (Fin.natAdd (UniformKPolynomial.Count d.source.arity) ⟨_,h⟩)
  else imaginaryEntry d
 def typedEquation (d : Data) (p : LocalAffineVariableLayout.Parameters d.source.arity) : Sparse.Poly (Width d) 1 :=
  Sparse.sub (NativeKForward.typedVertex (imaginaryEntry d) (sqrtEntry d) (sourceEntry d p.1) p.2)
    (SparseTransform.variableCode RationalCompiler.data (targetEntry d p))
 def typedBody (d : Data) : List (Sparse.Poly (Width d) 1) :=
  RuntimeTensorBasis.typedRows false false (imaginaryEntry d) (sqrtEntry d) ++
    (coefficientCatalogue d.source.arity).map (typedEquation d)

 theorem roots_exact (d : Data) : roots (encode d)=List.ofFn (rootFn d) := by
  unfold rootFn
  rw [OriginalFamilyPackingSource.ofFn_addCases]
  change OriginalFamilyPackingMachine.roots (RuntimeSupportTable.original d.source) ++ _ = _
  rw [RuntimeSupportTable.original,OriginalFamilyPackingSource.roots_exact]
  rfl
 theorem width_exact (d : Data) : width (encode d)=Width d := by
  rw [width,roots_exact,List.length_ofFn]
 theorem source_roots_length (d : Data) : (sourceRoots (encode d)).length=UniformKPolynomial.Count d.source.arity := by
  change (OriginalFamilyPackingMachine.roots (RuntimeSupportTable.original d.source)).length=_
  rw [RuntimeSupportTable.original,OriginalFamilyPackingSource.roots_exact,List.length_ofFn]
 theorem imaginary_exact (d : Data) : imaginary (encode d)=(imaginaryEntry d).val := by
  change 5+(OriginalFamilyPackingMachine.original (RuntimeSupportTable.original d.source)).length=_
  rw [RuntimeSupportTable.original,OriginalFamilyPackingSource.original_length]
  rfl
 theorem sqrt_exact (d : Data) : sqrt (encode d)=(sqrtEntry d).val := by
  rw [sqrt,imaginary_exact]
  rfl
 theorem keys_exact (d : Data) : keys (encode d)=
    (coefficientCatalogue d.source.arity).map (OriginalCatalogueSource.key d.source.arity) := by
  unfold keys
  change (List.range (OriginalCatalogueSource.family d.source.arity d.source.input).length).flatMap _ = _
  rw [OriginalCatalogueSource.family_length]
  have h : List.range d.source.count = (List.finRange d.source.count).map Fin.val := by simp
  rw [h]
  simp only [List.flatMap_map,coefficientCatalogue,List.map_flatMap]
  apply List.flatMap_congr
  intro i hi
  exact OriginalCatalogueSource.atVertex_exact d.source.arity d.source.input (.inl i)

 theorem equation_wire (d : Data) (i : Fin d.source.count) (x : Fin (d.source.arity i) → Bool) :
    equation (encode d,OriginalCatalogueSource.key d.source.arity ⟨.inl i,x⟩)=
      RationalInputMachine.rowWire (typedEquation d ⟨.inl i,x⟩) := by
  have ht : OriginalAddressTablesMachine.table ((source (encode d)).1,0,i.val) =
      (SparseTransform.allWords (d.source.arity i)).map (fun y => RationalTensorMachine.wireRow (y,sourceEntry d (.inl i) y)) := by
    rw [show (source (encode d)).1=OriginalCatalogueSource.family d.source.arity d.source.input from rfl,
      table_zero]
    rfl
  have ha : targetAddress (encode d,OriginalCatalogueSource.key d.source.arity ⟨.inl i,x⟩)=
      (targetEntry d ⟨.inl i,x⟩).val := by
    rw [targetAddress,source_roots_length]
    change _+OriginalCatalogueMachine.address (0,OriginalCatalogueMachine.catalogue
      (OriginalCatalogueSource.family d.source.arity d.source.input),OriginalCatalogueSource.key d.source.arity ⟨.inl i,x⟩)=_
    rw [address_zero]
    simp only [targetEntry,dite_eq_left (coefficientAddress_lt d.source.arity i x),bindings,Fin.val_natAdd]
    omega
  unfold equation
  change NativeKForward.vertex (layout (encode d),List.ofFn x,
    OriginalAddressTablesMachine.table ((source (encode d)).1,0,i.val)) ++
    RationalSparseMachine.neg (RationalSparseMachine.variable (width (encode d))
      (targetAddress (encode d,OriginalCatalogueSource.key d.source.arity ⟨.inl i,x⟩))) = _
  rw [ht]
  have hl : layout (encode d)=(Width d,(imaginaryEntry d).val,(sqrtEntry d).val) := by
    rw [layout,width_exact,imaginary_exact,sqrt_exact]
  rw [hl]
  have hv := NativeKForward.vertex_wire (imaginaryEntry d) (sqrtEntry d)
    (fun y : Fin (d.source.arity i) → Bool => sourceEntry d (.inl i) y) x
  change NativeKForward.vertex ((Width d,(imaginaryEntry d).val,(sqrtEntry d).val),List.ofFn x,
    (SparseTransform.allWords (d.source.arity i)).map (fun y => NativeKForward.wireRow (y,sourceEntry d (.inl i) y))) ++ _ = _
  have hvart : RationalSparseMachine.variable (width (encode d))
      (targetAddress (encode d,OriginalCatalogueSource.key d.source.arity ⟨.inl i,x⟩)) =
      RationalInputMachine.rowWire (SparseTransform.variableCode RationalCompiler.data (targetEntry d ⟨.inl i,x⟩)) :=
    (congrArg₂ RationalSparseMachine.variable (width_exact d) ha).trans
      (RationalSparseMachine.variable_wire (targetEntry d ⟨.inl i,x⟩))
  exact (congrArg₂ List.append hv (congrArg RationalSparseMachine.neg hvart)).trans
    (RationalSparseMachine.sub_wire _ _)

 theorem body_wire (d : Data) : body (encode d)=RationalInputMachine.bodyWire (typedBody d) := by
  unfold body
  rw [show layout (encode d)=(Width d,(imaginaryEntry d).val,(sqrtEntry d).val) from
    by rw [layout,width_exact,imaginary_exact,sqrt_exact],RuntimeTensorBasis.rows_wire,keys_exact]
  simp only [List.map_map,Function.comp_def,typedBody,RationalInputMachine.bodyWire,List.map_append]
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨i,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hp
  exact equation_wire d i x

 theorem request_exact (d : Data) : request (encode d)=RationalInputMachine.fromSource (rootFn d) (typedBody d) (bindings d) := by
  unfold request RationalInputMachine.fromSource
  congr 1
  · exact width_exact d
  · exact roots_exact d
  · exact body_wire d
  · simp only [addresses,roots_exact,List.length_ofFn,bindings,Fin.val_natAdd]
    rw [RuntimeTensorRowsSoundness.map_range_eq_ofFn]

 theorem guard_mem (d : Data) : SparseTransform.guard RationalCompiler.data (RootCount d) ∈ typedBody d := by
  simp [typedBody,RuntimeTensorBasis.typedRows]
 theorem roots_represented (d : Data) : ∀j,(rootFn d j).Represents (values d j : ℂ) := by
  intro j
  induction j using Fin.addCases with
  | left j => simpa only [rootFn,values,Fin.addCases_left] using UniformKPolynomial.descriptors_represents d.source.arity d.source.G d.source.input d.source.represented j
  | right j => simpa only [rootFn,values,Fin.addCases_right] using d.represented j
 theorem valid (d : Data) : OriginalSystemDecision.Valid (rootFn d) := ⟨values d,roots_represented d⟩
 def output (d : Data) : Option WitnessOutput.Output := WitnessOutput.originalOutput (rootFn d) (valid d) (typedBody d) (bindings d)
 theorem source_outputs (d : Data) : ∃ticks,Nonempty (TM2OutputsInTime machine.computer
    (inputEncoding.encode (encode d)) (some (WitnessOutput.resultEncoding.encode (output d))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := WitnessOutput.original_outputs (rootFn d) (valid d) (typedBody d) (bindings d)
  have left := requestExecutes.outputs (encode d)
  rw [request_exact] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩
 def witnessRuns : Runs inputEncoding WitnessOutput.resultEncoding encode output where
  machine := machine
  cost d := Classical.choose (source_outputs d)
  outputs d := Classical.choice (Classical.choose_spec (source_outputs d))
 theorem output_isSome_iff (d : Data) : (output d).isSome=true ↔
    ∃z : Fin (Width d) → ℂ,(∀j,z (bindings d j)=(values d j : ℂ)) ∧
      ∀p∈typedBody d,SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 := by
  rw [output,WitnessOutput.originalOutput_correct _ _ (values d) (roots_represented d) _ _ (guard_mem d)]
  exact exists_congr (fun z => RationalInputSystem.system_zero_iff (fun j => (values d j : ℂ)) (typedBody d) (bindings d) z)

 def Bound (d : Data) (z : Fin (Width d) → ℂ) : Prop := ∀j,z (bindings d j)=(values d j : ℂ)
 def targetCoefficient (d : Data) (i : Fin d.source.count) (x : Fin (d.source.arity i) → Bool) : AlgebraicComplex :=
  d.value ⟨(LocalAffineVariableLayout.address d.source.arity ⟨.inl i,x⟩).val,
    coefficientAddress_lt d.source.arity i x⟩
 def TargetMatches (d : Data) : Prop := ∀i x,targetCoefficient d i x=sourceKBasis.action (d.source.G i) x
 theorem bound_imaginary (d : Data) (z : Fin (Width d) → ℂ) (hb : Bound d z) :
    z (imaginaryEntry d)=(imaginaryUnit : ℂ) := by
  simpa only [imaginaryEntry,values,imaginaryIndex,UniformKPolynomial.values,Fin.addCases_left,Fin.addCases_right,
    Matrix.cons_val_zero] using hb (imaginaryIndex d)
 theorem bound_sqrt (d : Data) (z : Fin (Width d) → ℂ) (hb : Bound d z) :
    z (sqrtEntry d)=(sqrtTwo : ℂ) := by
  simpa only [sqrtEntry,values,sqrtIndex,UniformKPolynomial.values,Fin.addCases_left,Fin.addCases_right,
    Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.head_cons] using hb (sqrtIndex d)
 theorem bound_source (d : Data) (z : Fin (Width d) → ℂ) (hb : Bound d z)
    (i : Fin d.source.count) (x : Fin (d.source.arity i) → Bool) :
    z (sourceEntry d (.inl i) x)=(d.source.G i x : ℂ) := by
  simpa only [sourceEntry,values,oldIndex,UniformKPolynomial.values,Fin.addCases_left,
    OriginalFamilyInput.values,LocalAffineVariableLayout.get_address] using hb (oldIndex d ⟨.inl i,x⟩)
 theorem bound_target (d : Data) (z : Fin (Width d) → ℂ) (hb : Bound d z)
    (i : Fin d.source.count) (x : Fin (d.source.arity i) → Bool) :
    z (targetEntry d ⟨.inl i,x⟩)=(targetCoefficient d i x : ℂ) := by
  simpa only [targetEntry,dite_eq_left (coefficientAddress_lt d.source.arity i x),values,
    Fin.addCases_right,targetCoefficient] using hb
      (Fin.natAdd (UniformKPolynomial.Count d.source.arity)
        ⟨(LocalAffineVariableLayout.address d.source.arity ⟨.inl i,x⟩).val,
          coefficientAddress_lt d.source.arity i x⟩)
 theorem equation_eval (d : Data) (z : Fin (Width d) → ℂ) (hb : Bound d z)
    (i : Fin d.source.count) (x : Fin (d.source.arity i) → Bool) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z (typedEquation d ⟨.inl i,x⟩)=
      (sourceKBasis.action (d.source.G i) x : ℂ)-(targetCoefficient d i x : ℂ) := by
  unfold typedEquation
  rw [RuntimeTensorBasisSemantics.compilerData,SparseEvaluation.sub_eval]
  rw [NativeKForward.vertex_eval_map (algebraMap AlgebraicComplex ℂ) (imaginaryEntry d) (sqrtEntry d)
    (sourceEntry d (.inl i)) (d.source.G i) z
    (bound_imaginary d z hb) (bound_sqrt d z hb) (bound_source d z hb i) x]
  rw [SparseEvaluation.variable_eval,bound_target d z hb]
  rfl

 def fill (d : Data) : Fin (Width d) → ℂ := Fin.addCases ![1,0,0,1,1] (fun j => (values d j : ℂ))
 theorem fill_bound (d : Data) : Bound d (fill d) := by intro j; simp only [fill,bindings,Fin.addCases_right]
 theorem fill_guard (d : Data) : SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ)
    (fill d) (SparseTransform.guard RationalCompiler.data (RootCount d))=0 := by
  rw [RuntimeTensorBasisSemantics.compilerData,SparseEvaluation.guard_eval]
  simp [SymbolicTransform.matrix,SymbolicTransform.determinant,SparseTransform.point,
    SymbolicTransform.index,fill]
 theorem fill_matrix (d : Data) : SymbolicTransform.matrix (SparseTransform.point (fill d))=
    fun a b => (algebraMap AlgebraicComplex ℂ) ((RuntimeTensorBasisSemantics.basis false false).matrix a b) := by
  funext a b
  cases a <;> cases b <;>
    simp [SymbolicTransform.matrix,SparseTransform.point,SymbolicTransform.index,fill,
      RuntimeTensorBasisSemantics.basis,InvertibleKernel.identity,Holant.Signature.equality]
 theorem fill_basis (d : Data) : ∀p∈RuntimeTensorBasis.typedRows false false (imaginaryEntry d) (sqrtEntry d),
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill d) p=0 := by
  apply (RuntimeTensorBasisSemantics.rows_zero_iff_map (algebraMap AlgebraicComplex ℂ)
    (fill d) false false (imaginaryEntry d) (sqrtEntry d)
    (bound_imaginary d _ (fill_bound d)) (bound_sqrt d _ (fill_bound d))).mpr
  exact ⟨fill_guard d,fill_matrix d⟩
 theorem body_solutions_iff (d : Data) :
    (∃z : Fin (Width d) → ℂ,Bound d z ∧∀p∈typedBody d,
      SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔ TargetMatches d := by
  constructor
  · rintro ⟨z,hb,hbody⟩ i x
    have he := hbody (typedEquation d ⟨.inl i,x⟩)
      (List.mem_append_right _ (List.mem_map.mpr ⟨_,mem_coefficientCatalogue d.source.arity i x,rfl⟩))
    rw [equation_eval d z hb] at he
    exact (algebraMap AlgebraicComplex ℂ).injective (sub_eq_zero.mp he).symm
  · intro hm
    refine ⟨fill d,fill_bound d,List.forall_mem_append.mpr ⟨fill_basis d,?_⟩⟩
    intro e he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    rcases List.mem_flatMap.mp hp with ⟨i,hi,hp⟩
    rcases List.mem_map.mp hp with ⟨x,hx,rfl⟩
    rw [equation_eval d (fill d) (fill_bound d),hm i x,sub_self]
 theorem output_correct (d : Data) : (output d).isSome=true ↔ TargetMatches d :=
  (output_isSome_iff d).trans (body_solutions_iff d)

 theorem output_represents_iff (d : Data) : (output d).isSome=true ↔
    ∀(i : Fin d.source.count) (x : Fin (d.source.arity i) → Bool),
      (d.target ⟨(LocalAffineVariableLayout.address d.source.arity ⟨.inl i,x⟩).val,
        coefficientAddress_lt d.source.arity i x⟩).Represents (sourceKBasis.action (d.source.G i) x : ℂ) := by
  rw [output_correct]
  constructor
  · intro h i x
    have hr := d.represented ⟨(LocalAffineVariableLayout.address d.source.arity ⟨.inl i,x⟩).val,
      coefficientAddress_lt d.source.arity i x⟩
    change (d.target _).Represents (targetCoefficient d i x : ℂ) at hr
    rw [h i x] at hr
    exact hr
  · intro h i x
    apply (algebraMap AlgebraicComplex ℂ).injective
    exact RootCode.represents_unique (d.represented _) (h i x)

end
end Paper2.ExactInput.Recognition.NativeKSystem

