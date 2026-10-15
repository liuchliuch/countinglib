import ComplexCSP.Instances.MatrixCSPCodeMixed
import PlanarHom.GraphComponentSemantics
import PlanarHom.MaterializedFieldListMachines

set_option backward.isDefEq.respectTransparency false

/-! # Computed connected components for unrestricted binary CSP inputs

The actual occurrence-list algorithm preserves isolates, loops and repeated
constraints. No planarity condition is imposed on the source or queried codes.
-/
namespace ComplexCSP.MatrixCSPComponents
open PlanarHom PlanarHom.Complexity PairProjectionMachines
open ComplexityCSPCode MatrixCSPCodeMixed

variable {D K : Type} [Fintype D] (A : D → D → K)

def ConnectedValid (g : Code) : Prop :=
  Valid (MatrixCSP.language A) g ∧ (GraphComponentCode.support (toMixed g)).Connected ∧ 0 < g.vertices

def queries (g : Code) : List Code := (GraphComponentCode.components (toMixed g)).map MatrixCSPMixedAdapter.toCode

theorem queries_valid [CommSemiring K] (g : Code) (hg : Valid (MatrixCSP.language A) g)
    (q : Code) (hq : q ∈ queries g) : ConnectedValid A q := by
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
  have hv := GraphComponentCode.components_valid (toMixed g) (valid A g hg) c hc
  refine ⟨MatrixCSPMixedAdapter.valid A c hv,?_,GraphComponentCode.components_nonempty _ c hc⟩
  rw [toMixed_toCode c hv]
  exact GraphComponentCode.components_connected (toMixed g) (valid A g hg) c hc

theorem fp_queries : FP encoding encoding.list queries :=
  (fp_toMixed.comp GraphComponentMachines.fp_components).comp
    (ListMapMachines.fp_map MixedCode.encoding encoding MatrixCSPMixedAdapter.toCode MatrixCSPMixedAdapter.fp_toCode)

variable [Field K] [Algebra ℚ K] {dimension : ℕ}

omit [Algebra ℚ K] in
theorem partition_components (g : Code) (hg : Valid (MatrixCSP.language A) g) :
    partition (MatrixCSP.language A) g =
      ((queries g).map (partition (MatrixCSP.language A))).prod := by
  have hv := valid A g hg
  calc
    _ = (toMixed g).evaluate hv (fun _ : Fin 1 => A) (fun u : Fin 0 => u.elim0) (fun _ => 1) := by
      rw [←MatrixCSPMixedAdapter.partition_toCode, toCode_toMixed A g hg]
    _ = _ := by
      rw [GraphComponentCode.evaluate_components]
      unfold queries
      rw [List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro c hc
      have hc' := GraphComponentCode.components_valid (toMixed g) hv c hc
      rw [MixedCode.totalEvaluation_valid _ _ _ c hc']
      exact (MatrixCSPMixedAdapter.partition_toCode A c hc').symm

noncomputable def connectedProblem (basis : Module.Basis (Fin dimension) ℚ K) : PromiseProblem :=
  ⟨fun raw => ∃ g, ConnectedValid A g ∧ encoding.encode g = raw,
    encodedFunction encoding (numberFieldEncoding basis) (partition (MatrixCSP.language A)) []⟩

/-- A dynamic polynomial-size query list of genuinely computed components,
followed by exact multiplication of all answers. -/
noncomputable def reduction (basis : Module.Basis (Fin dimension) ℚ K) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis)
      (connectedProblem A basis) := by
  classical
  let prepare : Code → Bits × List Code := fun g => ([],queries g)
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare :=
    (fp_const encoding BitEncoding.bits []).pair fp_queries
  let recover : Bits × List K → K := fun p => p.2.prod
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (fp_snd _ _).comp (MaterializedFieldListMachines.fp_product basis)
  let target := ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis
  let source := connectedProblem A basis
  let view : ∀ raw, target.valid raw → Code := fun _ h => h.choose
  have hview : ∀ raw h, encoding.encode (view raw h)=raw := fun _ h => h.choose_spec.2
  let p := Classical.choose (exists_partition_output_bound (MatrixCSP.language A) basis)
  have hbound := Classical.choose_spec (exists_partition_output_bound (MatrixCSP.language A) basis)
  refine nonadaptiveReduction encoding BitEncoding.bits encoding (numberFieldEncoding basis)
    (numberFieldEncoding basis) target source prepare (partition (MatrixCSP.language A)) recover
    (Classical.choice hp) (Classical.choice hr) view hview ?_ ?_ ?_ p ?_
  · intro raw h q hq
    exact ⟨_,queries_valid A _ h.choose_spec.1 q hq,rfl⟩
  · intro q _
    exact encodedFunction_encode encoding (numberFieldEncoding basis) (partition (MatrixCSP.language A)) [] q
  · intro raw h
    change (numberFieldEncoding basis).encode
      (((queries (view raw h)).map (partition (MatrixCSP.language A))).prod) =
      encodedFunction encoding (numberFieldEncoding basis) (partition (MatrixCSP.language A)) [] raw
    conv_rhs => rw [←hview raw h,encodedFunction_encode]
    rw [←partition_components A _ h.choose_spec.1]
  · intro raw h
    obtain ⟨g,hg,rfl⟩ := h
    simpa only [source,connectedProblem,encodedFunction_encode] using hbound g

end ComplexCSP.MatrixCSPComponents
