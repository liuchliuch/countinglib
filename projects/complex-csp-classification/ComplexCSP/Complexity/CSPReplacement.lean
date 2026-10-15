import ComplexCSP.Complexity.CSPCountReduction
import ComplexCSP.Complexity.ProductReplacement

set_option backward.isDefEq.respectTransparency false

/-! # A genuine fixed-language product-replacement oracle reduction -/
namespace ComplexCSP.ComplexityCSPReplacement
open scoped BigOperators
open ComplexityCSPCode ComplexityCSPCountReduction
open PlanarHom PlanarHom.Complexity PairProjectionMachines
set_option maxHeartbeats 1200000
variable {D K : Type} [Fintype D] [Field K] [DecidableEq K]
variable {s : ℕ} (L : Language D K (Fin s))
variable (G : (i : Fin s) → (Fin (L.arity i) → D) → K)

def language : Language D K (Fin s) := ⟨L.arity,L.arity_pos,G⟩
def targetEntry : Entry L → K
  | none => 1
  | some i => G i.1 i.2
noncomputable def targetAlphabet : Fin (Fintype.card (Entry L)) → K :=
  fun i => targetEntry L G ((Fintype.equivFin (Entry L)).symm i)
noncomputable def table (m : ℕ) : List (K × K) :=
  ExponentProductTables.representatives (ComplexityCSPNodes.alphabet L) (targetAlphabet L G) m

omit [DecidableEq K] in
theorem target_words_product (g : Code) (σ : Fin g.vertices → D) :
    ((ComplexityCSPNodes.words L g σ).map (targetAlphabet L G)).prod =
      eval (language L G) g σ := by
  simp only [ComplexityCSPNodes.words,targetAlphabet,List.map_map,Function.comp_def,
    Equiv.symm_apply_apply,eval,assignmentWord]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [constraintEntry]
  split_ifs <;> first | rfl | contradiction

noncomputable def prepare (g : Code) : List (K × K) × List Code :=
  let ns := table L G g.constraints.length
  (ns,ComplexityCSPQueries.queries g ns.length)

def recover (p : List (K × K) × List K) : K :=
  MaterializedLagrangeRecoveryMachines.recover (p.1,p.2.tail)

variable [Algebra ℚ K] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
noncomputable def contextEncoding := ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list

theorem fp_prepare : FP encoding ((contextEncoding basis).prod encoding.list) (prepare L G) := by
  let e := numberFieldEncoding basis
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hm := (hv.comp (fp_snd _ _)).comp (ListUnaryLengthMachine.fp_length constraintEncoding)
  have ht := hm.comp (ExponentProductTables.fp_representatives basis
    (ComplexityCSPNodes.alphabet L) (targetAlphabet L G))
  have hn := ht.comp (ListUnaryLengthMachine.fp_length (e.prod e))
  have hq := (hn.pair (fp_id encoding)).comp ComplexityCSPQueries.fp_queries
  exact ht.pair hq

theorem fp_recover : FP ((contextEncoding basis).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis) (recover : List (K × K) × List K → K) := by
  let e := numberFieldEncoding basis
  have ht := fp_fst (contextEncoding basis) e.list
  have ha := (fp_snd (contextEncoding basis) e.list).comp (ListDecompositionMachines.fp_tail e 0)
  exact (ht.pair ha).comp (MaterializedLagrangeRecoveryMachines.fp_recover basis)

private theorem map_range_eq_ofFn {A : Type} (f : ℕ → A) (n : ℕ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj; simp

omit [Algebra ℚ K] in
theorem recovery_correct
    (hcompat : ProductCompatibility.Compatible (ComplexityCSPNodes.alphabet L) (targetAlphabet L G))
    (hzero : ∀ i, ComplexityCSPNodes.alphabet L i = 0 → targetAlphabet L G i = 0)
    (g : Code) :
    recover ((prepare L G g).1,(prepare L G g).2.map (partition L)) =
      partition (language L G) g := by
  have h := ComplexityProductReplacement.recover_word_products
    (ComplexityCSPNodes.alphabet L) (targetAlphabet L G) hcompat hzero
    (ComplexityCSPNodes.words L g) g.constraints.length (ComplexityCSPNodes.words_length L g)
  simp only [prepare,recover,ComplexityCSPQueries.queries,List.map_cons,List.tail_cons,
    List.map_map,Function.comp_def]
  rw [map_range_eq_ofFn]
  simp only [table,repeat_partition,ComplexityCSPNodes.words_product,
    target_words_product,partition,repeat_eval] at h ⊢
  convert h using 1 <;> rfl

/-- All preprocessing, comparisons, dynamic interpolation, and field output
lengths are charged by actual checked bit machines. -/
noncomputable def reduction
    (hcompat : ProductCompatibility.Compatible (ComplexityCSPNodes.alphabet L) (targetAlphabet L G))
    (hzero : ∀ i, ComplexityCSPNodes.alphabet L i = 0 → targetAlphabet L G i = 0) :
    PromisePolyTimeTuringReduction (partitionProblem (language L G) basis) (partitionProblem L basis) := by
  classical
  let p := Classical.choose (exists_partition_output_bound L basis)
  have hp := Classical.choose_spec (exists_partition_output_bound L basis)
  let target := partitionProblem (language L G) basis
  let source := partitionProblem L basis
  let view : ∀ raw,target.valid raw → Code := fun _ h => h.choose
  have hs : ∀ raw h, encoding.encode (view raw h)=raw := fun _ h => h.choose_spec.2
  refine nonadaptiveReduction encoding (contextEncoding basis) encoding
    (numberFieldEncoding basis) (numberFieldEncoding basis) target source (prepare L G)
    (partition L) recover (Classical.choice (fp_prepare L G basis))
    (Classical.choice (fp_recover basis)) view hs ?_ ?_ ?_ p ?_
  · intro raw h q hq
    refine ⟨q,?_,rfl⟩
    exact ComplexityCSPQueries.queries_valid L _ h.choose_spec.1 _ q hq
  · intro q _
    exact encodedFunction_encode encoding (numberFieldEncoding basis) (partition L) [] q
  · intro raw h
    change (numberFieldEncoding basis).encode
      (recover ((prepare L G (view raw h)).1,
        (prepare L G (view raw h)).2.map (partition L))) =
      encodedFunction encoding (numberFieldEncoding basis) (partition (language L G)) [] raw
    rw [recovery_correct L G hcompat hzero]
    conv_rhs => rw [←hs raw h,encodedFunction_encode]
  · intro raw h
    obtain ⟨g,hg,rfl⟩ := h
    simpa only [source,partitionProblem,encodedFunction_encode] using hp g

omit [Algebra ℚ K] [DecidableEq K] in
theorem absolute_alphabet (σ : K →+* ℂ)
    (habs : ∀ i a, σ (G i a) = (‖σ (L.value i a)‖ : ℂ)) :
    ∀ i, σ (targetAlphabet L G i) = (‖σ (ComplexityCSPNodes.alphabet L i)‖ : ℂ) := by
  intro i
  unfold targetAlphabet ComplexityCSPNodes.alphabet
  cases (Fintype.equivFin (Entry L)).symm i with
  | none => simp [targetEntry,entryValue]
  | some ia => exact habs ia.1 ia.2

noncomputable def absoluteReduction (σ : K →+* ℂ)
    (habs : ∀ i a, σ (G i a) = (‖σ (L.value i a)‖ : ℂ)) :
    PromisePolyTimeTuringReduction (partitionProblem (language L G) basis) (partitionProblem L basis) :=
  reduction L G basis
    (ComplexityProductReplacement.compatible_of_absolute_embedding σ _ _ (absolute_alphabet L G σ habs))
    (ComplexityProductReplacement.zeros_of_absolute_embedding σ _ _ (absolute_alphabet L G σ habs))

end ComplexCSP.ComplexityCSPReplacement
