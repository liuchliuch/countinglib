import ComplexCSP.Complexity.CSPQueries
import ComplexCSP.Complexity.NaturalDecoder
import PlanarHom.NonadaptiveReductionCompiler

/-!
# COUNT reduces to exact partition evaluation for a fixed finite language

The reduction's preprocessing and recovery are actual polynomial-time bit
machines, with canonical exact field outputs and explicitly bounded answer
lengths. It neither assumes nor proves the complexity dichotomy.
-/
namespace ComplexCSP.ComplexityCSPCountReduction
open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityCSPCode ComplexityCSPQueries
variable {D K : Type} [Fintype D] [Field K] [DecidableEq K] [Algebra ℚ K]
variable {s dimension : ℕ} (L : Language D K (Fin s))
variable (basis : Module.Basis (Fin dimension) ℚ K)

noncomputable def countEncoding : BitEncoding (Code × K) :=
  encoding.prod (numberFieldEncoding basis)
noncomputable def contextEncoding : BitEncoding (List K × K) :=
  (numberFieldEncoding basis).list.prod (numberFieldEncoding basis)

/-- Only valid canonical codes are in the source promise. Malformed words have
an explicit default answer but cannot carry advice to the reduction. -/
noncomputable def partitionProblem : PromiseProblem :=
  ⟨fun raw => ∃ g, Valid L g ∧ encoding.encode g = raw,
    encodedFunction encoding (numberFieldEncoding basis) (partition L) []⟩

noncomputable def countProblem : PromiseProblem :=
  ⟨fun raw => ∃ p : Code × K, Valid L p.1 ∧ (countEncoding basis).encode p = raw,
    encodedFunction (countEncoding basis) BitEncoding.nat (fun p => countAt L p.1 p.2) []⟩

noncomputable def prepare (p : Code × K) : (List K × K) × List Code :=
  let ns := ComplexityCSPNodes.nodes L p.1.constraints.length
  ((ns, p.2), queries p.1 ns.length)

noncomputable def recover (p : (List K × K) × List K) : ℕ :=
  ComplexityNaturalDecoder.decode basis
    (ComplexityCountRecovery.recover (p.2.headD 0) p.1.1 p.2.tail p.1.2)

/-- Actual preprocessing computes the distinct nonzero weights, then materializes
all repetition queries. Alphabet size and field degree are fixed constants. -/
theorem fp_prepare : FP (countEncoding basis) ((contextEncoding basis).prod encoding.list)
    (prepare L) := by
  let e := numberFieldEncoding basis
  have hg := fp_fst encoding e
  have hz := fp_snd encoding e
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices, g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hm := ((hg.comp hv).comp (fp_snd BitEncoding.unaryNat constraintEncoding.list)).comp
    (ListUnaryLengthMachine.fp_length constraintEncoding)
  have hn := hm.comp (ComplexityCSPNodes.fp_nodes L basis)
  have hc := hn.comp (ListUnaryLengthMachine.fp_length e)
  have hq := (hc.pair hg).comp fp_queries
  exact (hn.pair hz).pair hq

/-- No promise on moments is used by this machine. The semantic count theorem
below establishes correctness for the actual generated oracle answers. -/
theorem fp_recover : FP ((contextEncoding basis).prod (numberFieldEncoding basis).list)
    BitEncoding.nat (recover basis) := by
  let e := numberFieldEncoding basis
  let ec := contextEncoding basis
  have hx := fp_fst ec e.list
  have hy := fp_snd ec e.list
  have hn := hx.comp (fp_fst e.list e)
  have hz := hx.comp (fp_snd e.list e)
  have htotal := hy.comp (ListDecompositionMachines.fp_headD e 0)
  have hans := hy.comp (ListDecompositionMachines.fp_tail e 0)
  have hp := htotal.pair (hn.pair (hans.pair hz))
  exact (hp.comp (ComplexityCountRecovery.fp_recover basis)).comp
    (ComplexityNaturalDecoder.fp_decode basis)

private theorem map_range_eq_ofFn {A : Type} (f : ℕ → A) (n : ℕ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

/-- Exact recovery for literal oracle evaluations, including absent requested
weights, zero products, no constraints, and isolated variables. -/
theorem recovery_correct (p : Code × K) :
    recover basis ((prepare L p).1, (prepare L p).2.map (partition L)) = countAt L p.1 p.2 := by
  let g := p.1
  let m := g.constraints.length
  let ns := ComplexityCSPNodes.nodes L m
  let μ := ComplexityCSPNodes.node L m
  have h := ComplexityCountRecovery.recover_moments (eval L g) μ
    (ComplexityCSPNodes.node_injective L m) (ComplexityCSPNodes.node_nonzero L m)
    (ComplexityCSPNodes.eval_coverage L g) p.2
  have hn : ns = List.ofFn μ := ComplexityCSPNodes.nodes_eq_ofFn L m
  have hl : ns.length = (ExponentProductTables.representatives
      (ComplexityCSPNodes.alphabet L) (ComplexityCSPNodes.alphabet L) m).length := by
    simp only [ns, ComplexityCSPNodes.nodes, List.length_map]
  have he : ComplexityCountRecovery.recover
      (partition L (repeatCode g 0)) ns
      ((List.range ns.length).map (fun i => partition L (repeatCode g (i + 1)))) p.2 =
      (countAt L g p.2 : K) := by
    rw [map_range_eq_ofFn, hl, hn, zeroth_partition]
    simpa only [repeat_partition, Fintype.card_fun, Fintype.card_fin,
      ComplexityCountRecovery.count, countAt] using h
  have hd := congrArg (ComplexityNaturalDecoder.decode basis) he
  rw [ComplexityNaturalDecoder.decode_natCast] at hd
  simpa only [recover, prepare, queries, List.map_cons, List.headD_cons,
    List.tail_cons, List.map_map, Function.comp_def] using hd

/-- The full polynomial-time Turing reduction has an actual finite oracle
machine. Every query is a valid canonical CSP code, and all answer bits are
charged using the proved fixed-alphabet coordinate-height bound. -/
noncomputable def reduction :
    PromisePolyTimeTuringReduction (countProblem L basis) (partitionProblem L basis) := by
  classical
  let p := Classical.choose (exists_partition_output_bound L basis)
  have hp := Classical.choose_spec (exists_partition_output_bound L basis)
  let view : ∀ raw, (countProblem L basis).valid raw → Code × K :=
    fun _ h => h.choose
  have hs : ∀ raw h, (countEncoding basis).encode (view raw h) = raw :=
    fun _ h => h.choose_spec.2
  refine nonadaptiveReduction (countEncoding basis) (contextEncoding basis)
    encoding (numberFieldEncoding basis) BitEncoding.nat
    (countProblem L basis) (partitionProblem L basis) (prepare L) (partition L)
    (recover basis) (Classical.choice (fp_prepare L basis))
    (Classical.choice (fp_recover basis)) view hs ?_ ?_ ?_ p ?_
  · intro raw h q hq
    refine ⟨q, ?_, rfl⟩
    exact queries_valid L (view raw h).1 h.choose_spec.1 _ q hq
  · intro q _
    exact encodedFunction_encode encoding (numberFieldEncoding basis) (partition L) [] q
  · intro raw h
    change BitEncoding.nat.encode
      (recover basis ((prepare L (view raw h)).1,
        (prepare L (view raw h)).2.map (partition L))) =
      encodedFunction (countEncoding basis) BitEncoding.nat
        (fun p => countAt L p.1 p.2) [] raw
    conv_rhs => rw [← hs raw h, encodedFunction_encode]
    rw [recovery_correct]
  · intro raw h
    obtain ⟨g, hg, rfl⟩ := h
    simpa only [partitionProblem, encodedFunction_encode] using hp g

/-- Hence COUNT has a genuine fixed-language polynomial-time oracle reduction
without any supplied arithmetic routine, interpolation bound, or dichotomy. -/
theorem count_reduces_partition :
    Nonempty (PromisePolyTimeTuringReduction (countProblem L basis) (partitionProblem L basis)) :=
  ⟨reduction L basis⟩

end ComplexCSP.ComplexityCSPCountReduction
