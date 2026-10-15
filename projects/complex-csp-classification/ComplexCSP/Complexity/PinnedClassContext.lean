import ComplexCSP.Complexity.TypeStackConcrete
import ComplexCSP.Complexity.SupportUnaryPin

/-! # Shape-only context invariant for actual layer compilation

The restriction preserves literal input bytes and makes no semantic relation or
correctness assumption. The zero-dimensional fallback keeps the original CSP
instance and clears layers and witnesses.
-/
namespace ComplexCSP.ComplexityPinnedClass
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexitySupportWitnessPrimitives
open MaltsevWitness WeightedMaltsev
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def ShapedContext (c : ComplexityTypeStackConcrete.Context K) : Prop :=
  ∃ W : Code (Fin d) c.2.1, c.2.2=encodeCode W
abbrev Context (K : Type) (d : ℕ) :=
  {c : ComplexityTypeStackConcrete.Context K // ShapedContext (d:=d) c}
noncomputable def contextCode : BitEncoding (Context K d) :=
  (ComplexityTypeStackConcrete.contextCode basis).restrict (ShapedContext (d:=d))

omit [Algebra ℚ K] in
def packContext {n : ℕ} (base : ComplexityTypeRowCallback.Context K) (W : Code (Fin d) n) : Context K d :=
  ⟨(base,n,encodeCode W),W,rfl⟩

omit [Algebra ℚ K] in
def contextWitness (c : Context K d) : {W : RawWitness // ShapedWitness (d:=d) W} :=
  ⟨c.val.2.2,by obtain ⟨W,hW⟩ := c.property; exact ⟨c.val.2.1,W,hW⟩⟩

omit [DecidableEq K] in
theorem fp_contextView : FP (contextCode (d:=d) basis) (ComplexityTypeStackConcrete.contextCode basis)
    (fun c => c.val) := fp_code_view _ _ _ (fun _ => rfl)

omit [DecidableEq K] in
theorem fp_contextWitness : FP (contextCode (d:=d) basis) (shapedWitnessCode d) contextWitness := by
  have h := ((fp_contextView (d:=d) basis).comp (fp_snd (ComplexityTypeRowCallback.contextCode basis)
    (BitEncoding.unaryNat.prod witnessCode))).comp (fp_snd BitEncoding.unaryNat witnessCode)
  exact h.transportOutput (fun _ => rfl)


omit [Algebra ℚ K] in
def fallback (g : ComplexityCSPCode.Code) : Context K d :=
  packContext (g,[]) ({seed := none,lookup := fun _ _ => none} : Code (Fin d) 0)

omit [DecidableEq K] in
theorem fp_fallback : FP ComplexityCSPCode.encoding (contextCode (d:=d) basis) fallback := by
  have hb := (fp_id ComplexityCSPCode.encoding).pair
    (fp_const ComplexityCSPCode.encoding (ComplexityWeightedLayers.layerCode basis).list [])
  have hm := (fp_const ComplexityCSPCode.encoding BitEncoding.unaryNat 0).pair
    (fp_const ComplexityCSPCode.encoding witnessCode ([],[]))
  exact (hb.pair hm).transportOutput (fun _ => rfl)

end ComplexCSP.ComplexityPinnedClass
