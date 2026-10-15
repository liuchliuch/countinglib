import ComplexCSP.Complexity.WitnessReconstruction
import ComplexCSP.Complexity.CSPWordAssignment
import ComplexCSP.Complexity.EncodingBounds
import PlanarHom.ListContextFilterMachines

/-! # Actual fixed-field execution of materialized marginal layers

A class record stores its anchor, normalized-row sum, and literal class witness.
The raw evaluator selects by the proved witness membership machine, appends the
anchor, and collects the sum factor. Missing classes use a zero factor. Factors
are copied from input records and multiplied only by the proved final product
machine; no value-growth or function-evaluation oracle is assumed.
-/
namespace ComplexCSP.ComplexityWeightedLayers
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives

abbrev ClassRecord (K : Type) := ℕ × (K × (RawTable × MaybeWord))
abbrev Layer (K : Type) := List (ClassRecord K)
abbrev State (K : Type) := List ℕ × List K

variable {K : Type} [Field K] [Algebra ℚ K] {dimension d : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d)

noncomputable def classCode : BitEncoding (ClassRecord K) :=
  BitEncoding.nat.prod ((numberFieldEncoding basis).prod (tableCode.prod maybeCode))
noncomputable def layerCode : BitEncoding (Layer K) := (classCode basis).list
noncomputable def stateCode : BitEncoding (State K) := wordCode.prod (numberFieldEncoding basis).list

def matchesClass (word : List ℕ) (r : ClassRecord K) : Bool :=
  memberRaw d m (r.2.2.1,word,r.2.2.2)

def emptyRecord : ClassRecord K := (0,0,[],[])

def select (word : List ℕ) (layer : Layer K) : ClassRecord K :=
  (layer.filter (matchesClass m word)).headD emptyRecord

def step (s : State K) (layer : Layer K) : State K :=
  let r := select m s.1 layer
  (s.1 ++ [r.1], s.2 ++ [r.2.1])

theorem fp_matches : FP (wordCode.prod (classCode basis)) BitEncoding.bool
    (fun p => matchesClass m p.1 p.2) := by
  have hp := fp_fst wordCode (classCode basis)
  have hr := fp_snd wordCode (classCode basis)
  have hrest := hr.comp (fp_snd BitEncoding.nat
    ((numberFieldEncoding basis).prod (tableCode.prod maybeCode)))
  have hw := hrest.comp (fp_snd (numberFieldEncoding basis) (tableCode.prod maybeCode))
  have ht := hw.comp (fp_fst tableCode maybeCode)
  have hs := hw.comp (fp_snd tableCode maybeCode)
  exact (ht.pair (hp.pair hs)).comp (fp_memberRaw d m)

theorem fp_select : FP (wordCode.prod (layerCode basis)) (classCode basis)
    (fun p => select m p.1 p.2) :=
  (ListContextFilterMachines.fp_filterWithContext wordCode (classCode basis)
    (fun p => matchesClass m p.1 p.2) (fp_matches basis m)).comp
      (ListDecompositionMachines.fp_headD (classCode basis) emptyRecord)

/-- An actual FP step, including table membership and first matching selection. -/
theorem fp_step : FP ((stateCode basis).prod (layerCode basis)) (stateCode basis)
    (fun p => step m p.1 p.2) := by
  let ek := numberFieldEncoding basis
  have hs := fp_fst (stateCode basis) (layerCode basis)
  have hl := fp_snd (stateCode basis) (layerCode basis)
  have hp := hs.comp (fp_fst wordCode ek.list)
  have hf := hs.comp (fp_snd wordCode ek.list)
  have hr := (hp.pair hl).comp (fp_select basis m)
  have ha := hr.comp (fp_fst BitEncoding.nat (ek.prod (tableCode.prod maybeCode)))
  have hv := (hr.comp (fp_snd BitEncoding.nat (ek.prod (tableCode.prod maybeCode)))).comp
    (fp_fst ek (tableCode.prod maybeCode))
  have has := (ha.pair (fp_const _ wordCode [])).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  have hvs := (hv.pair (fp_const _ ek.list [])).comp (ListMutationMachines.fp_cons ek)
  exact ((hp.pair has).comp (ListMutationMachines.fp_append BitEncoding.nat)).pair
    ((hf.pair hvs).comp (ListMutationMachines.fp_append ek))

omit [Algebra ℚ K] in
/-- The selected record is input data or the one fixed zero-factor fallback. -/
theorem select_mem_or (word : List ℕ) (layer : Layer K) :
    select m word layer = emptyRecord ∨ select m word layer ∈ layer := by
  unfold select
  cases h : layer.filter (matchesClass m word) with
  | nil => exact Or.inl rfl
  | cons r rest =>
    right
    have hr : r ∈ layer.filter (matchesClass m word) := by rw [h]; exact List.mem_cons_self
    exact (List.mem_filter.mp hr).1

open ComplexityEncodingBounds

/-- Selected anchors/factors are copied from input records or fixed defaults. -/
theorem select_code_bounds (word : List ℕ) (layer : Layer K) (N : ℕ)
    (hN : ((layerCode basis).encode layer).length ≤ N) :
    (BitEncoding.nat.encode (select m word layer).1).length ≤
        N + ((numberFieldEncoding basis).encode (0 : K)).length + 1 ∧
    ((numberFieldEncoding basis).encode (select m word layer).2.1).length ≤
        N + ((numberFieldEncoding basis).encode (0 : K)).length + 1 := by
  rcases select_mem_or m word layer with h | h
  · rw [h]
    have hz := encodeNat_length_le 0
    dsimp only [emptyRecord]
    constructor <;> omega
  · have hr := (encoded_mem_le (classCode basis) h).trans hN
    simp only [classCode, BitEncoding.prod_length] at hr
    constructor <;> omega

omit [Algebra ℚ K] in
@[simp] theorem fold_step_lengths (s : State K) (layers : List (Layer K)) :
    (layers.foldl (step m) s).1.length = s.1.length + layers.length ∧
    (layers.foldl (step m) s).2.length = s.2.length + layers.length := by
  induction layers generalizing s with
  | nil => simp
  | cons layer rest ih =>
    simpa [List.foldl_cons, step, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (step m s layer)

theorem fold_step_entry_bounds (N : ℕ) (s : State K) (layers : List (Layer K))
    (hp : ∀ a ∈ s.1, (BitEncoding.nat.encode a).length ≤
      N + ((numberFieldEncoding basis).encode (0 : K)).length + 1)
    (hf : ∀ a ∈ s.2, ((numberFieldEncoding basis).encode a).length ≤
      N + ((numberFieldEncoding basis).encode (0 : K)).length + 1)
    (hl : ∀ layer ∈ layers, ((layerCode basis).encode layer).length ≤ N) :
    (∀ a ∈ (layers.foldl (step m) s).1, (BitEncoding.nat.encode a).length ≤
      N + ((numberFieldEncoding basis).encode (0 : K)).length + 1) ∧
    (∀ a ∈ (layers.foldl (step m) s).2, ((numberFieldEncoding basis).encode a).length ≤
      N + ((numberFieldEncoding basis).encode (0 : K)).length + 1) := by
  induction layers generalizing s with
  | nil => exact ⟨hp,hf⟩
  | cons layer rest ih =>
    have hs := select_code_bounds basis m s.1 layer N (hl layer List.mem_cons_self)
    apply ih (step m s layer)
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hp a ha
      · exact (List.mem_singleton.mp ha) ▸ hs.1
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hf a ha
      · exact (List.mem_singleton.mp ha) ▸ hs.2
    · intro layer h
      exact hl layer (List.mem_cons_of_mem _ h)

/-- A quadratic bound for every intermediate raw state. The coefficient only
contains the fixed encoding size of field zero, never a runtime oracle. -/
theorem step_prefix_bound (s : State K) (layers : List (Layer K)) (i : ℕ) :
    ((stateCode basis).encode ((layers.take i).foldl (step m) s)).length ≤
      (Polynomial.C (100*(((numberFieldEncoding basis).encode (0 : K)).length+2)) *
        (Polynomial.X+1)^2).eval
        (((stateCode basis).prod (layerCode basis).list).encode (s,layers)).length := by
  let Z := ((numberFieldEncoding basis).encode (0 : K)).length
  let N := (((stateCode basis).prod (layerCode basis).list).encode (s,layers)).length
  let B := N+Z+1
  have hN : N = 2*(2*(wordCode.encode s.1).length +
      ((numberFieldEncoding basis).list.encode s.2).length+1) +
      ((layerCode basis).list.encode layers).length+1 := by
    simp only [N, stateCode, BitEncoding.prod_length]
  have hpcode : (wordCode.encode s.1).length ≤ N := by omega
  have hfcode : ((numberFieldEncoding basis).list.encode s.2).length ≤ N := by omega
  have hlcode : ((layerCode basis).list.encode layers).length ≤ N := by omega
  have hp : ∀ a ∈ s.1, (BitEncoding.nat.encode a).length ≤ B := by
    intro a ha
    have h := (encoded_mem_le BitEncoding.nat ha).trans hpcode
    dsimp only [B]
    omega
  have hf : ∀ a ∈ s.2, ((numberFieldEncoding basis).encode a).length ≤ B := by
    intro a ha
    have h := (encoded_mem_le (numberFieldEncoding basis) ha).trans hfcode
    dsimp only [B]
    omega
  have hl : ∀ layer ∈ layers.take i, ((layerCode basis).encode layer).length ≤ N := by
    intro layer h
    exact (encoded_mem_le (layerCode basis) (List.mem_of_mem_take h)).trans hlcode
  have he := fold_step_entry_bounds basis m N s (layers.take i) hp hf hl
  have hlen := fold_step_lengths m s (layers.take i)
  have hp0 := (BitEncoding.list_length_le BitEncoding.nat s.1).trans hpcode
  have hf0 := (BitEncoding.list_length_le (numberFieldEncoding basis) s.2).trans hfcode
  have hl0 := (BitEncoding.list_length_le (layerCode basis) layers).trans hlcode
  have hpL : ((layers.take i).foldl (step m) s).1.length ≤ 2*N := by
    rw [hlen.1, List.length_take]
    omega
  have hfL : ((layers.take i).foldl (step m) s).2.length ≤ 2*N := by
    rw [hlen.2, List.length_take]
    omega
  have hps := encoded_list_le BitEncoding.nat ((layers.take i).foldl (step m) s).1 B he.1
  have hfs := encoded_list_le (numberFieldEncoding basis) ((layers.take i).foldl (step m) s).2 B he.2
  have hpm := Nat.mul_le_mul_left (6*B+3) hpL
  have hfm := Nat.mul_le_mul_left (6*B+3) hfL
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  change _ ≤ 100*(Z+2)*(N+1)^2
  simp only [stateCode, BitEncoding.prod_length]
  dsimp only [B] at hps hfs hpm hfm
  dsimp only [wordCode] at hps ⊢
  nlinarith [Nat.zero_le (Z*N^2)]

/-- Actual iteration over every materialized layer; supplied data need not be
valid mathematical classes for this FP claim. -/
theorem fp_fold : FP ((stateCode basis).prod (layerCode basis).list) (stateCode basis)
    (fun p => p.2.foldl (step m) p.1) :=
  ListFoldMachines.fp_foldl (layerCode basis) (stateCode basis) (step m)
    (fp_step basis m)
    (Polynomial.C (100*(((numberFieldEncoding basis).encode (0 : K)).length+2)) *
      (Polynomial.X+1)^2)
    (fun s layers i _ => step_prefix_bound basis m s layers i)

section Evaluation
variable {s : ℕ} (L : Language (Fin d) K (Fin s))

def finish (g : ComplexityCSPCode.Code) (state : State K) : K :=
  ComplexityCSPWordAssignment.assignmentWeight L g state.1 * state.2.prod

def execute (g : ComplexityCSPCode.Code) (initial : List ℕ) (layers : List (Layer K)) : K :=
  finish L g (layers.foldl (step m) (initial,[]))

/-- The terminal computation uses the actual fixed-table CSP assignment product. -/
theorem fp_finish :
    FP (ComplexityCSPCode.encoding.prod (stateCode basis)) (numberFieldEncoding basis)
      (fun p => finish L p.1 p.2) := by
  have hg := fp_fst ComplexityCSPCode.encoding (stateCode basis)
  have hs := fp_snd ComplexityCSPCode.encoding (stateCode basis)
  have hw := hs.comp (fp_fst wordCode (numberFieldEncoding basis).list)
  have hf := hs.comp (fp_snd wordCode (numberFieldEncoding basis).list)
  have hv := (hg.pair hw).comp (ComplexityCSPWordAssignment.fp_assignmentWeight L basis)
  have hp := hf.comp (MaterializedFieldListMachines.fp_product basis)
  exact (hv.pair hp).comp (FixedFieldArithmetic.fp_multiplication basis)

/-- Full ComputeF runtime on literal precomputed layer data. This does not assume
that arbitrary input layers are semantically valid marginal classes; that
separate invariant is proved when the layers are constructed. -/
theorem fp_execute :
    FP (ComplexityCSPCode.encoding.prod (wordCode.prod (layerCode basis).list))
      (numberFieldEncoding basis) (fun p => execute m L p.1 p.2.1 p.2.2) := by
  have hg := fp_fst ComplexityCSPCode.encoding (wordCode.prod (layerCode basis).list)
  have hr := fp_snd ComplexityCSPCode.encoding (wordCode.prod (layerCode basis).list)
  have hw := hr.comp (fp_fst wordCode (layerCode basis).list)
  have hl := hr.comp (fp_snd wordCode (layerCode basis).list)
  have hs := hw.pair (fp_const _ (numberFieldEncoding basis).list [])
  have he := (hs.pair hl).comp (fp_fold basis m)
  exact (hg.pair he).comp (fp_finish basis L)

end Evaluation

end ComplexCSP.ComplexityWeightedLayers
