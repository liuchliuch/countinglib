import ComplexCSP.Structure.WeightedMaltsevElimination
import ComplexCSP.Complexity.WeightedLayers

/-! # Literal typed-to-raw weighted layer interface -/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness
open ComplexityWitnessPrimitives ComplexityWitnessEncoding
variable {K : Type} [Field K] [DecidableEq K] {d n : ℕ}

def labelAnchor (label : RowLabel K d) : ℕ :=
  match label with
  | none => 0
  | some p => p.1.val

/-- This is the single shared class translation used by both semantics and
bit-size proofs. No field value is recomputed while translating a class. -/
def encodeClass (entry : RowLabel K d × StoredCode d n) : ComplexityWeightedLayers.ClassRecord K :=
  (labelAnchor entry.1, labelFactor entry.1, rawTable entry.2, maybeWord entry.2.seed)

def encodeLayer (layer : Layer K d n) : ComplexityWeightedLayers.Layer K :=
  layer.map encodeClass

/-- The list-backed search cache is already finite runtime data. This view only
changes materialized-vector labels to the fixed-row function codec. -/
def decodeTypeCache (cache : ListTypeCache (RowLabel K d)) :
    List (ℕ × List (ComplexityRowNormalization.Result K d)) :=
  cache.map (fun e => (e.1, e.2.map decodeLabel))


omit [DecidableEq K] in
theorem matchesClass_encode (m : Operation (Fin d)) (x : Tuple (Fin d) n)
    (entry : RowLabel K d × StoredCode d n) :
    ComplexityWeightedLayers.matchesClass (fun a b c => m (a,b,c)) (word x) (encodeClass entry) =
      member m entry.2.toCode x :=
  memberRaw_stored m entry.2 x

omit [DecidableEq K] in
theorem select_encode (m : Operation (Fin d)) (x : Tuple (Fin d) n) (layer : Layer K d n) :
    ComplexityWeightedLayers.select (fun a b c => m (a,b,c)) (word x) (encodeLayer layer) =
      ((selectRow m layer x).map encodeClass).getD ComplexityWeightedLayers.emptyRecord := by
  simp only [ComplexityWeightedLayers.select, encodeLayer, List.headD_eq_head?_getD,
    List.head?_filter, List.find?_map]
  have hp : (ComplexityWeightedLayers.matchesClass (fun a b c => m (a,b,c)) (word x)) ∘ encodeClass =
      (fun e : RowLabel K d × StoredCode d n => member m e.2.toCode x) := by
    funext e
    exact matchesClass_encode m x e
  rw [hp]
  rfl

theorem word_snocTuple (x : Tuple (Fin d) n) (a : Fin d) :
    word (snocTuple x a) = word x ++ [a.val] := by
  rw [← ComplexityCSPWordAssignment.assignmentLabels_tuple (g := ⟨n + 1, []⟩) (snocTuple x a),
    ← ComplexityCSPWordAssignment.assignmentLabels_tuple (g := ⟨n, []⟩) x]
  simp only [ComplexityCSPWordAssignment.assignmentLabels, view_snocTuple]
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]

section PositiveDomain
variable [NeZero d]

def chooseRow (m : Operation (Fin d)) (layer : Layer K d n) (x : Tuple (Fin d) n) : Fin d × K :=
  match selectRow m layer x with
  | none => (0, 0)
  | some entry => match entry.1 with
      | none => (0, 0)
      | some p => (p.1, labelFactor entry.1)

/-- The fallback choice is an actual domain value and has factor zero. -/
theorem chooseRow_factor {m : Operation (Fin d)} (hm : IsMaltsev m)
    (G : (Fin (n + 1) → Fin d) → K) (layer : Layer K d n) (hv : ValidLayer G layer)
    (hclasses : ∀ a, Preserves m (rowFiber G a)) (x : Tuple (Fin d) n) :
    marginal G (view x) = G (view (snocTuple x (chooseRow m layer x).1)) * (chooseRow m layer x).2 := by
  unfold chooseRow
  cases he : selectRow m layer x with
  | none =>
    have hz := marginal_zero_of_row_zero G _ ((selectRow_none hm G layer hv hclasses x).mp he)
    simpa only [mul_zero] using hz
  | some entry =>
    simp only []
    obtain ⟨hx, hl⟩ := selectRow_some hm G layer hv hclasses x he
    cases hp : entry.1 with
    | none => exact False.elim (hx ((tableLabel_none G _).mp (hl.trans hp)))
    | some p =>
      rcases p with ⟨a, w⟩
      simpa only [view_snocTuple] using marginal_factor G (view x) a w (hl.trans hp)

omit [DecidableEq K] in
theorem step_encode (m : Operation (Fin d)) (x : Tuple (Fin d) n) (factors : List K)
    (layer : Layer K d n) :
    ComplexityWeightedLayers.step (fun a b c => m (a,b,c)) (word x, factors) (encodeLayer layer) =
      (word (snocTuple x (chooseRow m layer x).1), factors ++ [(chooseRow m layer x).2]) := by
  simp only [ComplexityWeightedLayers.step, select_encode]
  unfold chooseRow
  cases he : selectRow m layer x with
  | none => simp [ComplexityWeightedLayers.emptyRecord, word_snocTuple]
  | some entry =>
    simp only []
    cases hl : entry.1 with
    | none => simp [encodeClass, labelAnchor, hl, labelFactor, word_snocTuple]
    | some p =>
      rcases p with ⟨a, w⟩
      simp [encodeClass, labelAnchor, hl, word_snocTuple]

end PositiveDomain
end ComplexCSP.WeightedMaltsev
