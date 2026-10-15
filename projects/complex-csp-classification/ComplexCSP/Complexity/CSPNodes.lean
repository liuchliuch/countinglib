import ComplexCSP.Complexity.CSPCode
import PlanarHom.ProductRepresentativeSemantics

/-! Actual polynomial-time distinct nonzero candidate weights of a fixed CSP language. -/
namespace ComplexCSP.ComplexityCSPNodes
open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityCSPCode
variable {D K : Type} [Fintype D] [Field K] [DecidableEq K]
variable {s : ℕ} (L : Language D K (Fin s))

/-- Fixed finite alphabet reindexing is program data, never a runtime oracle. -/
noncomputable def alphabet : Fin (Fintype.card (Entry L)) → K :=
  fun i => entryValue L ((Fintype.equivFin (Entry L)).symm i)

noncomputable def words (g : Code) (σ : Fin g.vertices → D) :
    List (Fin (Fintype.card (Entry L))) :=
  (assignmentWord L g σ).map (Fintype.equivFin (Entry L))

@[simp] theorem words_length (g : Code) (σ : Fin g.vertices → D) :
    (words L g σ).length = g.constraints.length := by simp [words]

theorem words_product (g : Code) (σ : Fin g.vertices → D) :
    ((words L g σ).map (alphabet L)).prod = eval L g σ := by
  simp [words, alphabet, List.map_map, eval, Function.comp_def]

/-- Exact weak-composition products, zero deletion, and stable numerical dedup. -/
noncomputable def nodes (m : ℕ) : List K :=
  (ExponentProductTables.representatives (alphabet L) (alphabet L) m).map Prod.fst

noncomputable def node (m : ℕ) :
    Fin (ExponentProductTables.representatives (alphabet L) (alphabet L) m).length → K :=
  ExponentProductTables.sourceNode (alphabet L) (alphabet L) m

theorem nodes_eq_ofFn (m : ℕ) : nodes L m = List.ofFn (node L m) := by
  unfold nodes node ExponentProductTables.sourceNode
  simpa only [List.map_ofFn, Function.comp_def] using
    (congrArg (List.map Prod.fst) (List.ofFn_get
      (ExponentProductTables.representatives (alphabet L) (alphabet L) m))).symm

theorem node_injective (m : ℕ) : Function.Injective (node L m) :=
  ExponentProductTables.sourceNode_injective _ _ _

theorem node_nonzero (m : ℕ) (i) : node L m i ≠ 0 :=
  ExponentProductTables.sourceNode_nonzero _ _ _ i

theorem nodes_length_le (m : ℕ) : (nodes L m).length ≤ (m + 1) ^ Fintype.card (Entry L) := by
  simpa only [nodes, List.length_map] using
    ExponentProductTables.representatives_length (alphabet L) (alphabet L) m

/-- Every nonzero actual assignment finds a retained numerical node. Zero is
handled separately by the zeroth query and never divided by. -/
theorem eval_coverage (g : Code) (σ : Fin g.vertices → D) (hz : eval L g σ ≠ 0) :
    ∃ i, node L g.constraints.length i = eval L g σ := by
  classical
  have hcompat : ProductCompatibility.Compatible (alphabet L) (alphabet L) :=
    fun _ _ _ _ _ h => h
  have hw := WordFrequencies.frequencies_mem_weak (words L g σ)
  rw [words_length] at hw
  have he := ExponentProductSemantics.value_frequencies (alphabet L) (words L g σ)
  rw [words_product] at he
  obtain ⟨i, hi, _⟩ := ExponentProductTables.exists_node_for_weak
    (alphabet L) (alphabet L) hcompat (WordFrequencies.frequencies (words L g σ)) hw
    (by rw [he]; exact hz)
  exact ⟨i, hi.trans he⟩

variable [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- Candidate generation, field equality and collision merging are actual FP
machines for the fixed field and alphabet; no candidate list is assumed. -/
theorem fp_nodes : FP BitEncoding.unaryNat (numberFieldEncoding basis).list (nodes L) := by
  exact (ExponentProductTables.fp_representatives basis (alphabet L) (alphabet L)).comp
    (ListMapMachines.fp_map _ _ Prod.fst (fp_fst _ _))

end ComplexCSP.ComplexityCSPNodes
