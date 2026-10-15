import ComplexCSP.Complexity.GadgetSubstitutionBounds
import ComplexCSP.Complexity.GadgetSubstitutionSemantics
import ComplexCSP.Complexity.CSPCountReduction

/-! # Lin's fixed-gadget transfer as a charged polynomial-time oracle reduction

The single query is built by the proved raw FP compiler. Query validity includes
the actual occurrence-degree predicate of the decoded finite instance. Exact
field output is copied, and all oracle answer bits are charged by the existing
fixed-language output bound.
-/
namespace ComplexCSP.ComplexityGadgetSubstitution
open ComplexityCSPCode PlanarHom PlanarHom.Complexity PairProjectionMachines

variable {D K : Type} [Fintype D] [Field K] [DecidableEq K] [Algebra ℚ K]
variable {s r dimension : ℕ} (L : Language D K (Fin s)) (M : Language D K (Fin r))
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- The degree promise uses literal scope-position counts after exact decoding. -/
def DegreeValid (δ : ℕ) (g : Code) : Prop :=
  ∃ hg : Valid L g, (toInstance L g hg).DegreeDivisible δ

/-- The ordinary canonical-code partition problem restricted only by the
specified occurrence-degree modulus. -/
noncomputable def degreePartitionProblem (δ : ℕ) : PromiseProblem :=
  ⟨fun raw => ∃ g, DegreeValid L δ g ∧ encoding.encode g = raw,
    encodedFunction encoding (numberFieldEncoding basis) (partition L) []⟩

variable {L M}

def prepare (P : GadgetSubstitution.Gadgets L M) (g : Code) : Bits × List Code :=
  ([],[compile (templates P) g])

def recover (p : Bits × List K) : K := p.2.headD 0

omit [Fintype D] [Field K] [DecidableEq K] [Algebra ℚ K] in
theorem fp_prepare (P : GadgetSubstitution.Gadgets L M) :
    FP encoding (BitEncoding.bits.prod encoding.list) (prepare P) := by
  have hc := ((fp_compile (templates P)).pair (fp_const encoding encoding.list [])).comp
    (ListMutationMachines.fp_cons encoding)
  exact (fp_const encoding BitEncoding.bits []).pair hc

omit [DecidableEq K] in
theorem fp_recover : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis) (recover : Bits × List K → K) :=
  (fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
    (ListDecompositionMachines.fp_headD (numberFieldEncoding basis) 0)

/-- Lin 2021 Lemma 7, with an actual machine, charged answers, and its exact
unrestricted-source to degree-restricted-target promise. -/
noncomputable def reduction (P : GadgetSubstitution.Gadgets L M)
    (hP : GadgetSubstitution.Realizes P) (δ : ℕ)
    (hdegree : ∀ j, (P j).DegreeDivisible δ) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem M basis)
      (degreePartitionProblem L basis δ) := by
  classical
  let p := Classical.choose (exists_partition_output_bound L basis)
  have hp := Classical.choose_spec (exists_partition_output_bound L basis)
  let target := ComplexityCSPCountReduction.partitionProblem M basis
  let source := degreePartitionProblem L basis δ
  let view : ∀ raw, target.valid raw → Code := fun _ h => h.choose
  have hs : ∀ raw h, encoding.encode (view raw h) = raw := fun _ h => h.choose_spec.2
  refine nonadaptiveReduction encoding BitEncoding.bits encoding
    (numberFieldEncoding basis) (numberFieldEncoding basis) target source
    (prepare P) (partition L) recover (Classical.choice (fp_prepare P))
    (Classical.choice (fp_recover basis)) view hs ?_ ?_ ?_ p ?_
  · intro raw h q hq
    have hq' : q = compile (templates P) (view raw h) := List.mem_singleton.mp hq
    subst q
    exact ⟨_, ⟨compile_valid P _ h.choose_spec.1,
      compile_degreeDivisible P δ hdegree _ h.choose_spec.1⟩, rfl⟩
  · intro q _
    exact encodedFunction_encode encoding (numberFieldEncoding basis) (partition L) [] q
  · intro raw h
    change (numberFieldEncoding basis).encode
      (partition L (compile (templates P) (view raw h))) =
      encodedFunction encoding (numberFieldEncoding basis) (partition M) [] raw
    conv_rhs => rw [← hs raw h, encodedFunction_encode]
    rw [compile_partition P hP _ h.choose_spec.1]
  · intro raw h
    obtain ⟨g, hg, rfl⟩ := h
    simpa only [source, degreePartitionProblem, encodedFunction_encode] using hp g

omit [DecidableEq K] in
/-- The actual degree-one promise is exactly the ordinary valid-code promise. -/
theorem degreePartitionProblem_one :
    degreePartitionProblem L basis 1 = ComplexityCSPCountReduction.partitionProblem L basis := by
  unfold degreePartitionProblem ComplexityCSPCountReduction.partitionProblem
  congr 1
  funext raw
  apply propext
  constructor
  · rintro ⟨g, ⟨hg, _⟩, he⟩
    exact ⟨g,hg,he⟩
  · rintro ⟨g,hg,he⟩
    exact ⟨g,⟨hg,fun _ => one_dvd _⟩,he⟩

/-- Ordinary fixed-gadget substitution, available without any degree condition. -/
noncomputable def unrestrictedReduction (P : GadgetSubstitution.Gadgets L M)
    (hP : GadgetSubstitution.Realizes P) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem M basis)
      (ComplexityCSPCountReduction.partitionProblem L basis) := by
  rw [← degreePartitionProblem_one (L := L) basis]
  exact reduction basis P hP 1 (fun _ _ => one_dvd _)

omit [DecidableEq K] in
/-- From literal degree-generated membership, the finite fixed presentations
supply the actual machine reduction. Selection is only of the fixed constants;
the varying-instance compiler and all complexity bounds are already proved. -/
theorem exists_reduction_of_degreeGenerated (δ : ℕ)
    (hM : ∀ j, DegreeGenerated L δ (M.value j)) :
    Nonempty (PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem M basis)
      (degreePartitionProblem L basis δ)) := by
  classical
  choose P hdegree hvalue using hM
  exact ⟨reduction basis P (fun j a => congrFun (hvalue j) a) δ hdegree⟩

end ComplexCSP.ComplexityGadgetSubstitution
