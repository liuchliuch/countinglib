import ComplexCSP.Structure.WeightedMaltsevRows

/-! # Computed weighted row layers and exact one-variable elimination -/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness
open scoped BigOperators
variable {K : Type} [Field K] [DecidableEq K] {d n : ℕ}

abbrev Layer (K : Type) (d n : ℕ) := List (RowLabel K d × StoredCode d n)

def rowFiber (G : (Fin (n + 1) → Fin d) → K) (L : RowLabel K d) : Set (Fin n → Fin d) :=
  {x | x ∈ rowSupport G ∧ tableLabel G x = L}

/-- Literal meaning of finite layer data: class witnesses and coverage. -/
def ValidLayer (G : (Fin (n + 1) → Fin d) → K) (layer : Layer K d n) : Prop :=
  (∀ e ∈ layer, Correct e.2.toCode (rowFiber G e.1)) ∧
    ∀ x ∈ rowSupport G, tableLabel G x ∈ layer.map Prod.fst

def buildLayer (m : Operation (Fin d)) (W : Code (Fin d) (n + 1))
    (evaluate : Tuple (Fin d) (n + 1) → K) (defaultValue : Fin d) : Layer K d n :=
  splitTypeClasses m (projectCode W n (Nat.le_succ n)) (rowLabel evaluate) defaultValue

omit [DecidableEq K] in
theorem projection_rowSupport (G : (Fin (n + 1) → Fin d) → K) :
    projection {x | G x ≠ 0} n (Nat.le_succ n) = rowSupport G := by
  ext x
  constructor
  · rintro ⟨y, hy, hpre⟩ hzero
    have he : y = Fin.snoc x (y (Fin.last n)) := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp
      · simpa only [show Fin.castLE (Nat.le_succ n) i = i.castSucc from Fin.ext rfl,
          Fin.snoc_castSucc]
          using hpre i
    have hz := congrFun hzero (y (Fin.last n))
    apply hy
    simpa [tableRows, ← he] using hz
  · intro hx
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hx
    exact ⟨Fin.snoc x a, ha, fun i => by
      rw [show Fin.castLE (Nat.le_succ n) i = i.castSucc from Fin.ext rfl]
      exact Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => Fin d) a x i⟩

theorem rowLabel_correct (evaluate : Tuple (Fin d) (n + 1) → K)
    (G : (Fin (n + 1) → Fin d) → K) (he : ∀ x, evaluate x = G (view x)) :
    rowLabel evaluate = fun x => tableLabel G (view x) := by
  funext x
  simp only [rowLabel, tableLabel]
  congr 1
  apply congrArg Vector.ofFn
  funext a
  rw [he, view_snocTuple]
  rfl

/-- The row layer is actually computed by splitting its projected support. -/
theorem buildLayer_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (n + 1)} (G : (Fin (n + 1) → Fin d) → K)
    (hW : Correct W {x | G x ≠ 0}) (hR : Preserves m (rowSupport G))
    (hTP : AllTypesPartition (rowSupport G) (fun x => tableLabel G (view x)))
    (hclasses : ∀ a, Preserves m (rowFiber G a))
    (evaluate : Tuple (Fin d) (n + 1) → K) (he : ∀ x, evaluate x = G (view x))
    (defaultValue : Fin d) : ValidLayer G (buildLayer m W evaluate defaultValue) := by
  have hP : Correct (projectCode W n (Nat.le_succ n)) (rowSupport G) := by
    simpa only [projection_rowSupport] using projectCode_correct hW n (Nat.le_succ n)
  have hl := rowLabel_correct evaluate G he
  have hcls : ∀ a, Preserves m (labelFiber (rowSupport G) (rowLabel evaluate) a) := by
    intro a
    simpa only [hl, labelFiber, view_ofFn, rowFiber] using hclasses a
  have htp : AllTypesPartition (rowSupport G) (rowLabel evaluate) := by rwa [hl]
  constructor
  · intro e he
    have h := splitTypeClasses_correct hm hR hP (rowLabel evaluate) htp hcls defaultValue e he
    simpa only [labelFiber, hl, view_ofFn, rowFiber] using h
  · intro x hx
    apply (splitTypeClasses_labels hm hR hP (rowLabel evaluate) htp defaultValue _).mpr
    exact ⟨x, hx, by simp only [hl, view_ofFn]⟩

def selectRow (m : Operation (Fin d)) (layer : Layer K d n) (x : Tuple (Fin d) n) :
    Option (RowLabel K d × StoredCode d n) :=
  layer.find? (fun e => member m e.2.toCode x)

theorem selectRow_some {m : Operation (Fin d)} (hm : IsMaltsev m)
    (G : (Fin (n + 1) → Fin d) → K) (layer : Layer K d n) (hv : ValidLayer G layer)
    (hclasses : ∀ a, Preserves m (rowFiber G a)) (x : Tuple (Fin d) n)
    {entry : RowLabel K d × StoredCode d n} (he : selectRow m layer x = some entry) :
    view x ∈ rowSupport G ∧ tableLabel G (view x) = entry.1 := by
  have hmem := List.mem_of_find?_eq_some he
  have hx := List.find?_some he
  exact (member_correct hm (hclasses entry.1) (hv.1 entry hmem) x).mp hx

theorem selectRow_none {m : Operation (Fin d)} (hm : IsMaltsev m)
    (G : (Fin (n + 1) → Fin d) → K) (layer : Layer K d n) (hv : ValidLayer G layer)
    (hclasses : ∀ a, Preserves m (rowFiber G a)) (x : Tuple (Fin d) n) :
    selectRow m layer x = none ↔ tableRows G (view x) = 0 := by
  constructor
  · intro he
    by_contra hn
    have hmem := hv.2 (view x) hn
    obtain ⟨entry, he_mem, hlabel⟩ := List.mem_map.mp hmem
    have hclass : view x ∈ rowFiber G entry.1 := ⟨hn, hlabel.symm⟩
    have ht := (member_correct hm (hclasses entry.1) (hv.1 entry he_mem) x).mpr hclass
    exact List.find?_eq_none.mp he entry he_mem ht
  · intro hz
    apply List.find?_eq_none.mpr
    intro entry he ht
    have hx := (member_correct hm (hclasses entry.1) (hv.1 entry he) x).mp ht
    exact hx.1 hz

def evaluateLayer (m : Operation (Fin d)) (layer : Layer K d n)
    (evaluateNext : Tuple (Fin d) (n + 1) → K) (x : Tuple (Fin d) n) : K :=
  match selectRow m layer x with
  | none => 0
  | some entry => match entry.1 with
      | none => 0
      | some p => evaluateNext (snocTuple x p.1) * labelFactor entry.1

/-- One step of ComputeF, including all cancellation and zero-row cases. -/
theorem evaluateLayer_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    (G : (Fin (n + 1) → Fin d) → K) (layer : Layer K d n) (hv : ValidLayer G layer)
    (hclasses : ∀ a, Preserves m (rowFiber G a))
    (evaluateNext : Tuple (Fin d) (n + 1) → K) (heval : ∀ x, evaluateNext x = G (view x))
    (x : Tuple (Fin d) n) : evaluateLayer m layer evaluateNext x = marginal G (view x) := by
  unfold evaluateLayer
  cases he : selectRow m layer x with
  | none => exact (marginal_zero_of_row_zero G _ ((selectRow_none hm G layer hv hclasses x).mp he)).symm
  | some entry =>
    simp only []
    obtain ⟨hx, hl⟩ := selectRow_some hm G layer hv hclasses x he
    cases hp : entry.1 with
    | none =>
      exact False.elim (hx ((tableLabel_none G _).mp (hl.trans hp)))
    | some p =>
      rcases p with ⟨a, w⟩
      simp only []
      rw [heval, view_snocTuple]
      exact (marginal_factor G (view x) a w (hl.trans hp)).symm

def retainedClasses (layer : Layer K d n) : Layer K d n :=
  layer.filter (fun e => decide (labelFactor e.1 ≠ 0))

def marginalSupportCode (m : Operation (Fin d)) (layer : Layer K d n) : StoredCode d n :=
  storeCode (unionCode m (retainedClasses layer) (fun e => e.2.toCode))

theorem retainedClasses_union (G : (Fin (n + 1) → Fin d) → K) (layer : Layer K d n)
    (hv : ValidLayer G layer) :
    familyUnion (retainedClasses layer) (fun e => rowFiber G e.1) = {x | marginal G x ≠ 0} := by
  ext x
  constructor
  · rintro ⟨entry, he, hx, hl⟩
    have hfactor : labelFactor entry.1 ≠ 0 := of_decide_eq_true (List.mem_filter.mp he).2
    exact (marginal_nonzero_iff G x).mpr ⟨hx, by rwa [hl]⟩
  · intro hx
    obtain ⟨hr, hf⟩ := (marginal_nonzero_iff G x).mp hx
    obtain ⟨entry, he, hl⟩ := List.mem_map.mp (hv.2 x hr)
    exact ⟨entry, List.mem_filter.mpr ⟨he, by simpa [hl] using hf⟩, hr, hl.symm⟩

/-- The next marginal support is computed by an actual witness-table union. -/
theorem marginalSupportCode_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    (G : (Fin (n + 1) → Fin d) → K) (layer : Layer K d n) (hv : ValidLayer G layer)
    (hclasses : ∀ a, Preserves m (rowFiber G a))
    (hmarg : Preserves m {x | marginal G x ≠ 0}) :
    Correct (marginalSupportCode m layer).toCode {x | marginal G x ≠ 0} := by
  have he := retainedClasses_union G layer hv
  have hu := unionCode_correct hm (indices := retainedClasses layer)
    (W := fun e => e.2.toCode) (R := fun e => rowFiber G e.1)
    (fun e he => hv.1 e (List.mem_filter.mp he).1)
    (fun e _ => hclasses e.1) (by rwa [he])
  simpa only [marginalSupportCode, storeCode_toCode, he] using hu

end ComplexCSP.WeightedMaltsev
