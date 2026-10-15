import Paper2.BellReduction.RawClosures

/-! Literal disjoint union with edge-address shifting. The graph compiler may
fix either component, while correctness retains every closed component and
nullary vertex of both original records. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.BellReduction.RawDisjointUnion
open Complexity NativeSmoothing NativeSmoothing.Surgery RawNative RawOccurrence

def shiftEnd (offset : ℕ) (p : RawEndpoint) : RawEndpoint := (offset+p.1,p.2)

def shiftRow (offset : ℕ) (v : RawVertex) : RawVertex := (v.1,v.2.map (shiftEnd offset))

def union (G H : RawClosedNetwork) : RawClosedNetwork where
  vertices := G.vertices ++ H.vertices.map (shiftRow G.edges.length)
  edges := G.edges ++ H.edges

 theorem shift_edgeEnds (offset count : ℕ) :
    (edgeEnds 0 count).map (shiftEnd offset) = edgeEnds offset count := by
  simp [edgeEnds,shiftEnd,List.map_flatMap,Function.comp_def]

 theorem endpoints_union (G H : RawClosedNetwork) :
    (union G H).endpoints = G.endpoints ++ H.endpoints.map (shiftEnd G.edges.length) := by
  simp [union,RawClosedNetwork.endpoints,shiftRow,List.map_map,List.map_flatten,Function.comp_def]

 theorem union_wellFormed {G H : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hH : H.WellFormed s b arity) :
    (union G H).WellFormed s b arity := by
  refine ⟨?_,?_,?_⟩
  · intro i
    have hm := List.get_mem (union G H).vertices i
    rcases List.mem_append.mp hm with hg | hh
    · obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
      rw [← hj]
      exact hG.1 j
    · obtain ⟨row,hr,he⟩ := List.mem_map.mp hh
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hr
      rw [← he,← hj]
      simpa [shiftRow] using hH.1 j
  · intro i
    have hm := List.get_mem (union G H).edges i
    rcases List.mem_append.mp hm with hg | hh
    · obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
      rw [← hj]
      exact hG.2.1 j
    · obtain ⟨j,hj⟩ := List.mem_iff_get.mp hh
      rw [← hj]
      exact hH.2.1 j
  · rw [endpoints_union,expectedEndpoints_eq]
    simp only [union,List.length_append]
    change List.Perm _ (edgeEnds 0 (G.edges.length+H.edges.length))
    rw [edgeEnds_add,Nat.zero_add,← shift_edgeEnds G.edges.length H.edges.length,← expectedEndpoints_eq G,
      ← expectedEndpoints_eq H]
    exact hG.2.2.append (hH.2.2.map _)

 theorem union_count (G H : RawClosedNetwork) :
    markedCount (union G H).vertices = markedCount G.vertices + markedCount H.vertices := by
  unfold markedCount union
  simp only [List.filter_append,List.length_append]
  congr 1
  exact mapped_count 0 H.vertices (shiftEnd G.edges.length)

 theorem readEnd_left {m n : ℕ} (z : Fin m → Bool) (w : Fin n → Bool)
    (p : RawEndpoint) (hp : p.1 < m) :
    readEnd (Fin.append z w) p = readEnd z p := by
  have hp' : p.1 < m+n := by omega
  simp only [readEnd,dif_pos hp,dif_pos hp']
  change (if p.2 then !(Fin.append z w (Fin.castAdd n ⟨p.1,hp⟩))
    else Fin.append z w (Fin.castAdd n ⟨p.1,hp⟩)) = _
  rw [Fin.append_left]

 theorem readEnd_right {m n : ℕ} (z : Fin m → Bool) (w : Fin n → Bool)
    (p : RawEndpoint) (hp : p.1 < n) :
    readEnd (Fin.append z w) (shiftEnd m p) = readEnd w p := by
  have hp' : m+p.1 < m+n := by omega
  simp only [readEnd,shiftEnd,dif_pos hp,dif_pos hp']
  change (if p.2 then !(Fin.append z w (Fin.natAdd m ⟨p.1,hp⟩))
    else Fin.append z w (Fin.natAdd m ⟨p.1,hp⟩)) = _
  rw [Fin.append_right]

 theorem row_left {K : Type} [CommSemiring K] (T : ℕ → List Bool → K)
    {m n : ℕ} (z : Fin m → Bool) (w : Fin n → Bool) (row : RawVertex)
    (hr : ∀ p ∈ row.2, p.1 < m) :
    rowValue T (Fin.append z w) row = rowValue T z row := by
  unfold rowValue
  congr 1
  exact List.map_congr_left (fun p hp => readEnd_left z w p (hr p hp))

 theorem row_right {K : Type} [CommSemiring K] (T : ℕ → List Bool → K)
    {m n : ℕ} (z : Fin m → Bool) (w : Fin n → Bool) (row : RawVertex)
    (hr : ∀ p ∈ row.2, p.1 < n) :
    rowValue T (Fin.append z w) (shiftRow m row) = rowValue T w row := by
  simp only [rowValue,shiftRow,List.map_map]
  congr 1
  exact List.map_congr_left (fun p hp => readEnd_right z w p (hr p hp))

/-- Independent native edge choices multiply the two original partition sums. -/
theorem union_value {K : Type} [CommSemiring K] (T : ℕ → List Bool → K)
    {G H : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hH : H.WellFormed s b arity) :
    evaluate T (union G H) = evaluate T G * evaluate T H := by
  have hedges : (union G H).edges.length = G.edges.length + H.edges.length :=
    List.length_append
  unfold evaluate
  rw [hedges]
  dsimp only [union]
  change (∑ c : Fin (G.edges.length+H.edges.length) → Bool,
    ((G.vertices ++ H.vertices.map (shiftRow G.edges.length)).map (rowValue T c)).prod) = _
  rw [← (Fin.appendEquiv G.edges.length H.edges.length).sum_comp,Fintype.sum_prod_type]
  have hg (z : Fin G.edges.length → Bool) (w : Fin H.edges.length → Bool) :
      (G.vertices.map (rowValue T (Fin.append z w))) = G.vertices.map (rowValue T z) := by
    apply List.map_congr_left
    intro row hr
    exact row_left T z w row (fun p hp => endpoint_bound hG hr hp)
  have hh (z : Fin G.edges.length → Bool) (w : Fin H.edges.length → Bool) :
      ((H.vertices.map (shiftRow G.edges.length)).map (rowValue T (Fin.append z w))) =
        H.vertices.map (rowValue T w) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro row hr
    exact row_right T z w row (fun p hp => endpoint_bound hH hr hp)
  change (∑ z : Fin G.edges.length → Bool, ∑ w : Fin H.edges.length → Bool,
    ((G.vertices ++ H.vertices.map (shiftRow G.edges.length)).map
      (rowValue T (Fin.append z w))).prod) = _
  simp only [List.map_append,List.prod_append,hg,hh]
  rw [Finset.sum_mul_sum]

end Paper2.BellReduction.RawDisjointUnion
