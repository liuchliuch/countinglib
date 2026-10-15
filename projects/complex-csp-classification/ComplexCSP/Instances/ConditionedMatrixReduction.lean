import ComplexCSP.Instances.ConditionedMatrixMachines

/-! # Charged arbitrary-color conditioning through one shared root

For each fixed color z the whole matrix A(i,j)A(i,z)A(j,z) is available from
A on unrestricted graphs. The number of queries is fixed with the language,
not with the number of input vertices. All queries are actual finite gadgets.
-/
namespace ComplexCSP.ConditionedMatrixCode
open PlanarHom PlanarHom.Complexity PairProjectionMachines
open ComplexityCSPCode ComplexityGadgetSubstitution RootedCSPProjection
open scoped BigOperators

variable {D K : Type} [Fintype D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [Algebra ℚ K] {dimension : ℕ}

/-- The actual list of fixed root attachments, each with fresh hidden variables. -/
def queries (A : D → D → K) (z : D) (P : RootedCSPProjection.Data (MatrixCSP.language A) (fun _ : Fin 1 => z))
    (g : Code) : List Code :=
  (List.ofFn P.gadgets).map (fun Q => query Q (rootCode g))

omit [LinearOrder K] [IsStrictOrderedRing K] [Algebra ℚ K] in
theorem fp_queries (A : D → D → K) (z : D)
    (P : RootedCSPProjection.Data (MatrixCSP.language A) (fun _ : Fin 1 => z)) :
    FP encoding encoding.list (queries A z P) := by
  exact fp_fixedList encoding encoding (List.ofFn P.gadgets)
    (fun g Q => query Q (rootCode g)) (fun Q _ => fp_rootCode.comp (fp_query Q))

omit [LinearOrder K] [IsStrictOrderedRing K] [Algebra ℚ K] in
theorem queries_valid (A : D → D → K) (z : D)
    (P : RootedCSPProjection.Data (MatrixCSP.language A) (fun _ : Fin 1 => z))
    (g : Code) (hg : Valid (MatrixCSP.language (conditioned A z)) g)
    (q : Code) (hq : q ∈ queries A z P g) : Valid (MatrixCSP.language A) q := by
  obtain ⟨Q,_,rfl⟩ := List.mem_map.mp hq
  rw [← rootedPresentation_code A (conditioned A z) g hg]
  exact query_valid Q _

omit [LinearOrder K] [IsStrictOrderedRing K] [Algebra ℚ K] in
theorem recover_queries (A : D → D → K) (z : D)
    (P : RootedCSPProjection.Data (MatrixCSP.language A) (fun _ : Fin 1 => z))
    (g : Code) (hg : Valid (MatrixCSP.language (conditioned A z)) g) :
    RootedCSPRecovery.recover P.coefficients
      ((queries A z P g).map (partition (MatrixCSP.language A))) =
        partition (MatrixCSP.language (conditioned A z)) g := by
  simp only [queries,List.map_ofFn,RootedCSPRecovery.recover]
  rw [← rootedPresentation_table A z g hg,P.correct]
  apply Finset.sum_congr rfl
  intro j _
  rw [← query_partition]
  rw [rootedPresentation_code]
  simp

/-- Genuine polynomial-time Turing reduction for one arbitrary fixed color.
No planarity, twin-freeness, positivity, or nonsingularity is imposed on A. -/
noncomputable def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (A : D → D → K) (z : D) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language (conditioned A z)) basis)
      (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) := by
  classical
  let P := RootedCSPProjection.choose (MatrixCSP.language A) (fun _ : Fin 1 => z)
  let prepare : Code → Bits × List Code := fun g => ([],queries A z P g)
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare :=
    (fp_const encoding BitEncoding.bits []).pair (fp_queries A z P)
  let recover : Bits × List K → K := fun p => RootedCSPRecovery.recover P.coefficients p.2
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (fp_snd _ _).comp (RootedCSPRecovery.fp_recover basis P.coefficients)
  let target := ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language (conditioned A z)) basis
  let source := ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis
  let view : ∀ raw, target.valid raw → Code := fun _ h => h.choose
  have hview : ∀ raw h, encoding.encode (view raw h) = raw := fun _ h => h.choose_spec.2
  let p := Classical.choose (exists_partition_output_bound (MatrixCSP.language A) basis)
  have hbound := Classical.choose_spec (exists_partition_output_bound (MatrixCSP.language A) basis)
  refine nonadaptiveReduction encoding BitEncoding.bits encoding (numberFieldEncoding basis)
    (numberFieldEncoding basis) target source prepare (partition (MatrixCSP.language A)) recover
    (Classical.choice hp) (Classical.choice hr) view hview ?_ ?_ ?_ p ?_
  · intro raw h q hq
    exact ⟨_,queries_valid A z P _ h.choose_spec.1 q hq,rfl⟩
  · intro q _
    exact encodedFunction_encode encoding (numberFieldEncoding basis)
      (partition (MatrixCSP.language A)) [] q
  · intro raw h
    change (numberFieldEncoding basis).encode
      (RootedCSPRecovery.recover P.coefficients
        ((queries A z P (view raw h)).map (partition (MatrixCSP.language A)))) =
      encodedFunction encoding (numberFieldEncoding basis)
        (partition (MatrixCSP.language (conditioned A z))) [] raw
    conv_rhs => rw [← hview raw h,encodedFunction_encode]
    rw [recover_queries A z P _ h.choose_spec.1]
  · intro raw h
    obtain ⟨g,hg,rfl⟩ := h
    simpa only [source,ComplexityCSPCountReduction.partitionProblem,encodedFunction_encode] using hbound g

end ComplexCSP.ConditionedMatrixCode
