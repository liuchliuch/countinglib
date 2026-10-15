import ComplexCSP.Algebra.GramPowerGadget
import ComplexCSP.Complexity.TupleExpansion
import ComplexCSP.Complexity.GadgetSubstitutionSemantics
import ComplexCSP.Complexity.GadgetSubstitutionBounds
import ComplexCSP.Complexity.CSPCountReduction

/-! # The Gram and two-power edge construction as a bit-costed oracle reduction

Tuple-colored graph vertices are first expanded to their coordinate variables.
Every directed edge is then replaced by the explicit fixed two-power gadget.
The raw compiler, all query words and all field-answer bits are charged.
-/
namespace ComplexCSP.ComplexityGramReduction
open ComplexityCSPCode PlanarHom PlanarHom.Complexity PairProjectionMachines
variable {D K : Type} [Fintype D] {r : ℕ}
section Semiring
variable [CommSemiring K]
variable (F : (Fin (r+1) → D) → K) (p q : ℕ) (hr : 0<r)

def sourceLanguage := GramPowerGadget.matrixLanguage (GramPowerGadget.matrix F p q)
def flatLanguage := ComplexityTupleExpansion.language (sourceLanguage F p q) hr

def presentations : GadgetSubstitution.Gadgets (GramGadget.language F) (flatLanguage F p q hr) :=
  fun _ => GramPowerGadget.gadget F p q

theorem realizes : GadgetSubstitution.Realizes (presentations F p q hr) := by
  intro i a
  exact GramPowerGadget.table_gadget F p q a

def compile (g : Code) : Code :=
  ComplexityGadgetSubstitution.compile
    (ComplexityGadgetSubstitution.templates (presentations F p q hr))
    (ComplexityTupleExpansion.compile r g)

theorem compile_valid (g : Code) (hg : Valid (sourceLanguage F p q) g) :
    Valid (GramGadget.language F) (compile F p q hr g) :=
  ComplexityGadgetSubstitution.compile_valid (presentations F p q hr) _
    (ComplexityTupleExpansion.valid_compile _ hr g hg)

theorem compile_partition (g : Code) (hg : Valid (sourceLanguage F p q) g) :
    partition (GramGadget.language F) (compile F p q hr g) =
      partition (sourceLanguage F p q) g := by
  rw [compile,ComplexityGadgetSubstitution.compile_partition
    (presentations F p q hr) (realizes F p q hr) _
    (ComplexityTupleExpansion.valid_compile _ hr g hg)]
  exact ComplexityTupleExpansion.partition_compile _ hr g hg

theorem fp_compile : FP encoding encoding (compile F p q hr) :=
  (ComplexityTupleExpansion.fp_compile r).comp
    (ComplexityGadgetSubstitution.fp_compile
      (ComplexityGadgetSubstitution.templates (presentations F p q hr)))

end Semiring

section Field
variable [Field K] [DecidableEq K] [Algebra ℚ K] {dimension : ℕ}
variable (F : (Fin (r+1) → D) → K) (p q : ℕ) (hr : 0<r)
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- Exact evaluation of the directed two-power matrix reduces to the original
single-table CSP. This supplies the literal reduction in Cai–Chen Lemmas 3, 4
and 23; it does not assume those lemmas' unresolved hardness conclusions. -/
noncomputable def reduction : PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem (sourceLanguage F p q) basis)
    (ComplexityCSPCountReduction.partitionProblem (GramGadget.language F) basis) := by
  classical
  let prepare : Code → Bits × List Code := fun g => ([],[compile F p q hr g])
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare := by
    have hq := ((fp_compile F p q hr).pair (fp_const encoding encoding.list [])).comp
      (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hq
  let recover : Bits × List K → K := fun a => a.2.headD 0
  have hrecover : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list)
      (numberFieldEncoding basis) recover :=
    (fp_snd _ _).comp (ListDecompositionMachines.fp_headD (numberFieldEncoding basis) 0)
  let source := ComplexityCSPCountReduction.partitionProblem (GramGadget.language F) basis
  let target := ComplexityCSPCountReduction.partitionProblem (sourceLanguage F p q) basis
  let view : ∀ raw,target.valid raw → Code := fun _ h => h.choose
  have hs : ∀ raw h, encoding.encode (view raw h)=raw := fun _ h => h.choose_spec.2
  let bound := Classical.choose (exists_partition_output_bound (GramGadget.language F) basis)
  have hbound := Classical.choose_spec (exists_partition_output_bound (GramGadget.language F) basis)
  refine nonadaptiveReduction encoding BitEncoding.bits encoding
    (numberFieldEncoding basis) (numberFieldEncoding basis) target source prepare
    (partition (GramGadget.language F)) recover (Classical.choice hp)
    (Classical.choice hrecover) view hs ?_ ?_ ?_ bound ?_
  · intro raw h out hout
    have he : out = compile F p q hr (view raw h) := List.mem_singleton.mp hout
    subst out
    exact ⟨_,compile_valid F p q hr _ h.choose_spec.1,rfl⟩
  · intro out _
    exact encodedFunction_encode encoding (numberFieldEncoding basis)
      (partition (GramGadget.language F)) [] out
  · intro raw h
    change (numberFieldEncoding basis).encode
      (partition (GramGadget.language F) (compile F p q hr (view raw h))) =
      encodedFunction encoding (numberFieldEncoding basis) (partition (sourceLanguage F p q)) [] raw
    rw [compile_partition F p q hr _ h.choose_spec.1]
    conv_rhs => rw [←hs raw h,encodedFunction_encode]
  · intro raw h
    obtain ⟨g,hg,rfl⟩ := h
    simpa only [source,ComplexityCSPCountReduction.partitionProblem,encodedFunction_encode] using hbound g

end Field
end ComplexCSP.ComplexityGramReduction
