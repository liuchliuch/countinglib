import ComplexCSP.Complexity.PinnedClassContext
import ComplexCSP.Complexity.MarginalSupport
import ComplexCSP.Structure.WeightedMaltsevPinnedOuter

set_option backward.isDefEq.respectTransparency false

/-! # Actual FP outer-frame update and shape preservation

The frame contains only the original instance, accumulated literal layers,
a unary dimension and a materialized support witness. The update compiler
copies the immutable instance, prepends one computed layer and invokes the
actual marginal-support machine. Shape preservation is independent of relation
correctness and block orthogonality.
-/
namespace ComplexCSP.ComplexityPinnedOuter
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexitySupportWitnessPrimitives
open ComplexityTypeStackMachines MaltsevWitness MaltsevRelations WeightedMaltsev
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K) (m : Fin d → Fin d → Fin d → Fin d)

/-- Unary predecessor is computed by a bounded conversion, never an unbounded
binary-to-unary expansion. -/
theorem fp_unaryPred : FP BitEncoding.unaryNat BitEncoding.unaryNat (fun n => n-1) := by
  have hn := UnaryNatConversionMachine.fp_conversion
  have hd := (hn.pair (fp_const BitEncoding.unaryNat BitEncoding.nat 1)).comp BinaryArithmetic.fp_subtraction
  have hmin : FP (BitEncoding.unaryNat.prod BitEncoding.nat) BitEncoding.unaryNat
      (fun p => min p.1 p.2) := ⟨BoundedUnaryMachines.computer⟩
  exact (((fp_id BitEncoding.unaryNat).pair hd).comp hmin).congr
    (fun n => min_eq_right (Nat.sub_le n 1))

abbrev RawContext (K : Type) := ComplexityTypeStackConcrete.Context K
abbrev FrameInput (K : Type) := RawContext K × ComplexityWeightedLayers.Layer K
noncomputable def frameCode : BitEncoding (FrameInput K) :=
  (ComplexityTypeStackConcrete.contextCode basis).prod (ComplexityWeightedLayers.layerCode basis)

def update (p : FrameInput K) : RawContext K :=
  ((p.1.1.1,p.2::p.1.1.2),p.1.2.1-1,ComplexityMarginalSupport.build m (p.1.2.1-1,p.2))

theorem fp_update : FP (frameCode basis) (ComplexityTypeStackConcrete.contextCode basis) (update m) := by
  let ec := ComplexityTypeStackConcrete.contextCode basis
  let eb := ComplexityTypeRowCallback.contextCode basis
  let el := ComplexityWeightedLayers.layerCode basis
  have hc := fp_fst ec el
  have hl := fp_snd ec el
  have hb := hc.comp (fp_fst eb (BitEncoding.unaryNat.prod witnessCode))
  have hg := hb.comp (fp_fst ComplexityCSPCode.encoding el.list)
  have hls := hb.comp (fp_snd ComplexityCSPCode.encoding el.list)
  have hnextLayers := (hl.pair hls).comp (ListMutationMachines.fp_cons el)
  have hn := (hc.comp (ComplexityTypeStackConcrete.fp_dimensionOf basis)).comp fp_unaryPred
  have hW := (hn.pair hl).comp (ComplexityMarginalSupport.fp_build basis m)
  exact (hg.pair hnextLayers).pair (hn.pair hW)

omit [Algebra ℚ K] in
def LayerShape (n : ℕ) (layer : ComplexityWeightedLayers.Layer K) : Prop :=
  ∃ typed : Layer K d n, layer = encodeLayer typed

omit [Algebra ℚ K] in
theorem update_shaped (operation : Operation (Fin d)) (c : RawContext K)
    (layer : ComplexityWeightedLayers.Layer K) (h : LayerShape (d:=d) (c.2.1-1) layer) :
    ComplexityPinnedClass.ShapedContext (d:=d) (update (fun a b c => operation (a,b,c)) (c,layer)) := by
  obtain ⟨typed,rfl⟩ := h
  refine ⟨(marginalSupportCode operation typed).toCode,?_⟩
  change ComplexityMarginalSupport.build (fun a b c => operation (a,b,c)) (c.2.1-1,encodeLayer typed) = _
  rw [ComplexityMarginalSupport.build_encode,encodeCode_stored]

omit [Algebra ℚ K] in
/-- One literal update agrees with the mathematical pinned-constructor step
whenever supplied its actual computed layer. -/
theorem update_encode (L : Language (Fin d) K (Fin s)) (operation : Operation (Fin d))
    (a : Fin d) (g : ComplexityCSPCode.Code) {n : ℕ} (W : StoredCode d (n+1))
    (layers : List (ComplexityWeightedLayers.Layer K)) :
    update (fun a b c => operation (a,b,c))
      (ComplexityTypeStackConcrete.storedContext (g,layers) W,
        encodeLayer (buildPinnedLayer operation W.toCode
          (fun x => ComplexityWeightedLayers.execute (fun a b c => operation (a,b,c)) L g (word x) layers) a)) =
      ComplexityTypeStackConcrete.storedContext
        (g,(pinnedOuterStep L operation a g W layers).2)
        (pinnedOuterStep L operation a g W layers).1 := by
  simp only [update,ComplexityTypeStackConcrete.storedContext,Nat.add_sub_cancel,
    ComplexityMarginalSupport.build_encode,pinnedOuterStep]

end ComplexCSP.ComplexityPinnedOuter
