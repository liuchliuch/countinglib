import Paper2.BellReduction.NativeSmoothing.Correctness

/-! The eliminator searches the actual label stream. No chosen vertex or
incident edge is an extra part of the input. -/
namespace Paper2.BellReduction.NativeSmoothing.Surgery
open Complexity RawClosedNetwork Smoothing
variable {K : Type} [CommSemiring K]

def occurrences (label : ℕ) (r : RawClosedNetwork) : ℕ :=
  (r.vertices.filter (fun row => row.1 == label)).length

/-- Exact outcomes of the literal search, including the empty-marker case. -/
theorem selected (r : RawClosedNetwork) {s b : ℕ} {arity : ℕ → ℕ}
    (hr : r.WellFormed s b arity) (label : ℕ) (ha : arity label = 2) :
    (occurrences label r = 0 ∧ Smoothing.compile label r = ⟨r,false⟩) ∨
    ∃ (v : Fin r.vertices.length) (p q : RawEndpoint),
      (r.vertices.get v).1 = label ∧ (r.vertices.get v).2 = [p,q] ∧
      Smoothing.compile label r = smoothAt r v.val p q := by
  let idx := r.vertices.findIdx (fun row => row.1 == label)
  by_cases hi : idx < r.vertices.length
  · let v : Fin r.vertices.length := ⟨idx,hi⟩
    have hl : (r.vertices.get v).1 = label := by
      have hh := @List.findIdx_getElem RawVertex (fun row => row.1 == label) r.vertices hi
      simpa only [beq_iff_eq,List.get_eq_getElem] using hh
    have hlen : (r.vertices.get v).2.length = 2 := by rw [(hr.1 v).2,hl,ha]
    obtain ⟨p,q,hrow⟩ := List.length_eq_two.mp hlen
    right
    refine ⟨v,p,q,hl,hrow,?_⟩
    have hg : r.vertices[idx]? = some (r.vertices.get v) := List.getElem?_eq_getElem hi
    change (match (r.vertices[idx]?).map Prod.snd with
      | some [first,second] => smoothAt r idx first second
      | _ => ⟨r,false⟩) = _
    rw [hg]
    simp only [Option.map_some,hrow]
    rfl
  · have hlen : idx = r.vertices.length := Nat.le_antisymm List.findIdx_le_length (by omega)
    have hn : ∀ row ∈ r.vertices, (row.1 == label) = false := List.findIdx_eq_length.mp hlen
    have hf : r.vertices.filter (fun row => row.1 == label) = [] :=
      List.filter_eq_nil_iff.mpr (fun row hv => by simp [hn row hv])
    left
    refine ⟨by simp [occurrences,hf],?_⟩
    simp only [Smoothing.compile,
      show r.vertices.findIdx (fun row => row.1 == label) = r.vertices.length from hlen,
      List.getElem?_length,Option.map_none]

 theorem compile_wellFormed (r : RawClosedNetwork) {s b : ℕ} {arity : ℕ → ℕ}
    (hr : r.WellFormed s b arity) (label : ℕ) (ha : arity label = 2) :
    (Smoothing.compile label r).query.WellFormed s b arity := by
  rcases selected r hr label ha with ⟨_,he⟩ | ⟨v,p,q,_,hrow,he⟩
  · simpa only [he] using hr
  · rw [he]
    apply smoothAt_wellFormed r hr v p q hrow
    intro row hm
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((List.eraseIdx_sublist r.vertices v.val).subset hm)
    rw [← hi]
    exact hr.1 i

 theorem compile_value (T : Choice.Table K) (r : RawClosedNetwork)
    {s b : ℕ} {arity : ℕ → ℕ} (hr : r.WellFormed s b arity)
    (label : ℕ) (ha : arity label = 2)
    (hT : ∀ a b, T label [a,b] = Signature.disequality a b) :
    RawNative.evaluate T r = (if (Smoothing.compile label r).circle then 2 else 1) *
      RawNative.evaluate T (Smoothing.compile label r).query := by
  rcases selected r hr label ha with ⟨_,he⟩ | ⟨v,p,q,hlabel,hrow,he⟩
  · simp [he]
  · rw [he]
    exact raw_smooth_value T r hr v p q hrow (by simpa only [hlabel] using hT)

 theorem mapped_count (label : ℕ) (rows : List RawVertex) (f : RawEndpoint → RawEndpoint) :
    ((rows.map (fun row => (row.1,row.2.map f))).filter
      (fun row => row.1 == label)).length = (rows.filter (fun row => row.1 == label)).length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.map_cons,List.filter_cons]; split <;> simp_all

 theorem smooth_count (r : RawClosedNetwork) (label : ℕ)
    (v : Fin r.vertices.length) (hv : (r.vertices.get v).1 = label) (p q : RawEndpoint) :
    occurrences label (smoothAt r v.val p q).query + 1 = occurrences label r := by
  have hp := (List.getElem_cons_eraseIdx_perm v.isLt).filter (fun row : RawVertex => row.1 == label)
  have hc := hp.length_eq
  have hlabel : r.vertices[v.val].1 = label := hv
  simp only [List.filter_cons,hlabel,beq_self_eq_true,ite_true,List.length_cons] at hc
  unfold smoothAt
  split <;> simp only [occurrences,emit,mapped_count] <;> omega

/-- Each compiled round removes exactly one marker if one exists. -/
theorem compile_count (r : RawClosedNetwork) {s b : ℕ} {arity : ℕ → ℕ}
    (hr : r.WellFormed s b arity) (label : ℕ) (ha : arity label = 2) :
    occurrences label (Smoothing.compile label r).query = occurrences label r - 1 := by
  rcases selected r hr label ha with ⟨hc,he⟩ | ⟨v,p,q,hlabel,_,he⟩
  · simp [he,hc]
  · rw [he]
    have hh := smooth_count r label v hlabel p q
    omega

end Paper2.BellReduction.NativeSmoothing.Surgery
