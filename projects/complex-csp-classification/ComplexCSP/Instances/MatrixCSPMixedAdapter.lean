import ComplexCSP.Algebra.PositiveBinaryApex
import ComplexCSP.Complexity.CSPCountReduction
import PlanarHom.MixedEvaluationPromises
import PlanarHom.MixedUnaryParallelMachines
import PlanarHom.GraphCodeNormalization

set_option backward.isDefEq.respectTransparency false

/-! # Actual raw mixed-graph to binary CSP adapter

The source promise includes ordinary planarity and all successfully decoded
representations. The target is the unrestricted canonical CSP codec. The
machine normalizes input words, preserves vertex and edge occurrences, and
never needs to decide planarity.
-/
namespace ComplexCSP.MatrixCSPMixedAdapter
open PlanarHom PlanarHom.Complexity PairProjectionMachines
open scoped BigOperators

abbrev Edge := ℕ × (ℕ × ℕ)
def edgeConstraint (e : Edge) : ℕ × List ℕ := (0,[e.1,e.2.1])
def toCode (g : MixedCode) : ComplexityCSPCode.Code :=
  ⟨g.vertices,g.edges.map edgeConstraint⟩

section Semiring
variable {D K : Type} [Fintype D] [CommSemiring K]

theorem constraint_valid (A : D → D → K) (g : MixedCode) (e : Edge)
    (he : e.1 < g.vertices ∧ e.2.1 < g.vertices ∧ e.2.2 < 1) :
    ComplexityCSPCode.ConstraintValid (MatrixCSP.language A) (toCode g).vertices (edgeConstraint e) := by
  refine ⟨Nat.zero_lt_one, rfl, ?_⟩
  intro v hv
  simp [edgeConstraint] at hv
  rcases hv with rfl | rfl
  · exact he.1
  · exact he.2.1

theorem valid (A : D → D → K) (g : MixedCode) (hg : g.Valid 1 0) :
    ComplexityCSPCode.Valid (MatrixCSP.language A) (toCode g) := by
  intro c hc
  change c ∈ g.edges.map edgeConstraint at hc
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
  exact constraint_valid A g e (hg.1 e he)

theorem unaries_nil (g : MixedCode) (hg : g.Valid 1 0) : g.unaries = [] := by
  cases h : g.unaries with
  | nil => rfl
  | cons u us =>
    have hu := hg.2 u (by rw [h]; simp)
    omega

theorem constraint_value (A : D → D → K) (g : MixedCode) (e : Edge)
    (he : e.1 < g.vertices ∧ e.2.1 < g.vertices ∧ e.2.2 < 1)
    (σ : Fin g.vertices → D) :
    ComplexityCSPCode.entryValue (MatrixCSP.language A)
      (ComplexityCSPCode.constraintEntry (MatrixCSP.language A) (toCode g) σ (edgeConstraint e)) =
      MixedCode.binaryValue g.vertices 1 (fun _ : Fin 1 => A) σ e := by
  rw [ComplexityCSPCode.constraintEntry,dif_pos (constraint_valid A g e he)]
  simp [ComplexityCSPCode.entryValue,MatrixCSP.language,ComplexityCSPCode.scope,
    edgeConstraint,MixedCode.binaryValue,he]

/-- Exact value identity, retaining isolated variables, loops and parallel edges. -/
theorem partition_toCode (A : D → D → K) (g : MixedCode) (hg : g.Valid 1 0) :
    ComplexityCSPCode.partition (MatrixCSP.language A) (toCode g) =
      g.evaluate hg (fun _ : Fin 1 => A) (fun u : Fin 0 => u.elim0) (fun _ => 1) := by
  simp only [MixedCode.evaluate,unaries_nil g hg,List.map_nil,List.prod_nil,mul_one,
    Finset.prod_const_one,one_mul]
  unfold ComplexityCSPCode.partition ComplexityCSPCode.eval ComplexityCSPCode.assignmentWord
  change (∑ σ : Fin g.vertices → D,
    (((g.edges.map edgeConstraint).map
      (ComplexityCSPCode.constraintEntry (MatrixCSP.language A) (toCode g) σ)).map
      (ComplexityCSPCode.entryValue (MatrixCSP.language A))).prod) = _
  simp only [List.map_map,Function.comp_def]
  apply Finset.sum_congr rfl
  intro σ _
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  exact constraint_value A g e (hg.1 e he) σ

end Semiring

private def edgeEncoding : BitEncoding Edge :=
  BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)

theorem fp_edgeConstraint : FP edgeEncoding ComplexityCSPCode.constraintEncoding edgeConstraint := by
  have hu := fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hv := (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  have htail := (hv.pair (fp_const edgeEncoding BitEncoding.nat.list [])).comp
    (ListMutationMachines.fp_cons BitEncoding.nat)
  have hscope := (hu.pair htail).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  exact (fp_const edgeEncoding BitEncoding.nat 0).pair hscope

theorem fp_toCode : FP MixedCode.encoding ComplexityCSPCode.encoding toCode := by
  have hc := MixedCode.fp_edges.comp
    (ListMapMachines.fp_map edgeEncoding ComplexityCSPCode.constraintEncoding edgeConstraint fp_edgeConstraint)
  exact (MixedCode.fp_vertices.pair hc).transportOutput (fun _ => rfl)

private def rawView (raw : Bits) (h : MixedCode.PlanarInput 1 0 raw) :
    BitEncoding.ValidWord MixedCode.encoding :=
  ⟨raw,by obtain ⟨g,hd,_⟩ := h; exact ⟨g,hd⟩⟩

private theorem rawView_valid (raw : Bits) (h : MixedCode.PlanarInput 1 0 raw) :
    (rawView raw h).value.Valid 1 0 := by
  obtain ⟨g,hd,hg⟩ := h
  have he : (rawView raw ⟨g,hd,hg⟩).value = g := BitEncoding.ValidWord.value_eq hd
  rw [he]
  exact hg.1

section Field
variable {D K : Type} [Fintype D] [Field K] [Algebra ℚ K] {dimension : ℕ}

/-- Real normalization and charged single-query reduction from the planar
mixed-code problem to unrestricted binary CSP evaluation. -/
noncomputable def reduction (basis : Module.Basis (Fin dimension) ℚ K) (A : D → D → K) :
    PromisePolyTimeTuringReduction
      (MixedCode.evaluationProblem basis (fun _ : Fin 1 => A)
        (fun u : Fin 0 => u.elim0) (fun _ => 1))
      (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) := by
  classical
  let target := MixedCode.evaluationProblem basis (fun _ : Fin 1 => A)
    (fun u : Fin 0 => u.elim0) (fun _ => 1)
  let source := ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis
  let e := BitEncoding.ValidWord.encoding MixedCode.encoding
  let prepare : BitEncoding.ValidWord MixedCode.encoding → Bits × List ComplexityCSPCode.Code :=
    fun w => ([],[toCode w.value])
  have hn : FP e ComplexityCSPCode.encoding (fun w => toCode w.value) :=
    (show FP e MixedCode.encoding BitEncoding.ValidWord.value from ⟨MixedCode.normalizer⟩).comp fp_toCode
  have hp : FP e (BitEncoding.bits.prod ComplexityCSPCode.encoding.list) prepare :=
    (fp_const e BitEncoding.bits []).pair
      ((hn.pair (fp_const e ComplexityCSPCode.encoding.list [])).comp
        (ListMutationMachines.fp_cons ComplexityCSPCode.encoding))
  let recover : Bits × List K → K := fun p => p.2.headD 0
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (fp_snd _ _).comp (ListDecompositionMachines.fp_headD (numberFieldEncoding basis) 0)
  let p := Classical.choose (ComplexityCSPCode.exists_partition_output_bound (MatrixCSP.language A) basis)
  have hbound := Classical.choose_spec
    (ComplexityCSPCode.exists_partition_output_bound (MatrixCSP.language A) basis)
  refine nonadaptiveReduction e BitEncoding.bits ComplexityCSPCode.encoding
    (numberFieldEncoding basis) (numberFieldEncoding basis) target source prepare
    (ComplexityCSPCode.partition (MatrixCSP.language A)) recover (Classical.choice hp)
    (Classical.choice hr) rawView (fun _ _ => rfl) ?_ ?_ ?_ p ?_
  · intro raw h q hq
    have he : q = toCode (rawView raw h).value := List.mem_singleton.mp hq
    subst q
    exact ⟨_,valid A _ (rawView_valid raw h),rfl⟩
  · intro q _
    exact encodedFunction_encode ComplexityCSPCode.encoding (numberFieldEncoding basis)
      (ComplexityCSPCode.partition (MatrixCSP.language A)) [] q
  · intro raw h
    change (numberFieldEncoding basis).encode
      (ComplexityCSPCode.partition (MatrixCSP.language A) (toCode (rawView raw h).value)) =
      MixedCode.evaluationValue basis (fun _ : Fin 1 => A)
        (fun u : Fin 0 => u.elim0) (fun _ => 1) raw
    rw [partition_toCode A _ (rawView_valid raw h)]
    exact (MixedCode.evaluationValue_decode basis _ _ _ raw (rawView raw h).value
      (BitEncoding.ValidWord.decode_raw (rawView raw h)) (rawView_valid raw h)).symm
  · intro raw h
    obtain ⟨g,hg,rfl⟩ := h
    simpa only [source,ComplexityCSPCountReduction.partitionProblem,encodedFunction_encode] using hbound g

end Field
end ComplexCSP.MatrixCSPMixedAdapter
