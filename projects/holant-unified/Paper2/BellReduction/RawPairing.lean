import Paper2.BellReduction.RawTripleBridge

/-! Literal two-occurrence reconnection on original ordered endpoint lists.
The three fixed modes are the 12|34, 13|24 and 14|23 native closures. -/
namespace Paper2.BellReduction.RawPairing
open Complexity RawOccurrence RawTripleBridge
open BellMachines.RawTriple

def rest (G : RawClosedNetwork) : List RawVertex :=
  G.vertices.filter (fun v => v != selected G 0 && v != selected G 1)

def endpoint (G : RawClosedNetwork) (i j : ℕ) : RawEndpoint :=
  (selected G i).2.getD j (0,false)

def rows (mode : Fin 3) (p q r s : RawEndpoint) (tail : List RawVertex) : List RawVertex :=
  if mode.val = 0 then (0,[p,q])::(0,[r,s])::tail else
  if mode.val = 1 then (0,[p,r])::(0,[q,s])::tail else
    (0,[p,s])::(0,[q,r])::tail

def query (mode : Fin 3) (G : RawClosedNetwork) : RawClosedNetwork where
  vertices := rows mode (endpoint G 0 0) (endpoint G 0 1)
    (endpoint G 1 0) (endpoint G 1 1) (rest G)
  edges := G.edges

/-- Actual first-two extraction from the unchanged input label stream. -/
theorem selected_two {G : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hzero : arity 0 = 2)
    (hc : 2 ≤ markedCount G.vertices) :
    ∃ p q r t tail,
      G.vertices.Perm ((0,[p,q])::(0,[r,t])::tail) ∧
      endpoint G 0 0 = p ∧ endpoint G 0 1 = q ∧
      endpoint G 1 0 = r ∧ endpoint G 1 1 = t ∧ rest G = tail := by
  obtain ⟨a,vs,ha⟩ := popMarked_exists (vs := G.vertices) (by omega)
  have hca := popMarked_count ha
  obtain ⟨b,tail,hb⟩ := popMarked_exists (vs := vs) (by omega)
  have hp := (popMarked_perm ha).trans (List.Perm.cons _ (popMarked_perm hb))
  have hlen (ps : List RawEndpoint) (hm : (0,ps) ∈ G.vertices) : ps.length = 2 := by
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
    have hh := (hG.1 i).2
    rw [hi] at hh
    exact hh.trans hzero
  obtain ⟨p,q,rfl⟩ := List.length_eq_two.mp (hlen a (hp.mem_iff.mpr (by simp)))
  obtain ⟨r,t,rfl⟩ := List.length_eq_two.mp (hlen b (hp.mem_iff.mpr (by simp)))
  have hn := marked_nodup hG hzero
  have hna := popMarked_nodup ha hn
  have hm := popMarked_marked ha
  rw [popMarked_marked hb] at hm
  have hs0 : selected G 0 = (0,[p,q]) := by
    change (RawTripleBridge.marked G.vertices).getD 0 (0,[]) = _
    rw [hm]
    rfl
  have hs1 : selected G 1 = (0,[r,t]) := by
    change (RawTripleBridge.marked G.vertices).getD 1 (0,[]) = _
    rw [hm]
    rfl
  refine ⟨p,q,r,t,tail,hp,?_,?_,?_,?_,?_⟩
  · simp [endpoint,hs0]
  · simp [endpoint,hs0]
  · simp [endpoint,hs1]
  · simp [endpoint,hs1]
  · unfold rest
    rw [hs0,hs1,popMarked_filter hb hna,popMarked_filter ha hn]
    simp only [List.filter_filter]
    congr 1
    funext v
    ac_rfl

 theorem rows_endpoints (mode : Fin 3) (p q r s : RawEndpoint) (tail : List RawVertex) :
    ((rows mode p q r s tail).map Prod.snd).flatten.Perm
      ([p,q,r,s] ++ (tail.map Prod.snd).flatten) := by
  apply List.perm_iff_count.mpr
  intro e
  unfold rows
  split <;> (try split) <;>
    simp only [List.map_cons,List.flatten_cons,List.count_append,List.count_cons,
      List.count_nil,List.nil_append] <;> omega

 theorem query_wellFormed {G : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hzero : arity 0 = 2)
    (hc : 2 ≤ markedCount G.vertices) (mode : Fin 3) :
    (query mode G).WellFormed s b arity := by
  obtain ⟨p,q,r,t,tail,hp,hp0,hp1,hq0,hq1,hr⟩ := selected_two hG hzero hc
  have he : (query mode G).vertices = rows mode p q r t tail := by
    simp only [query,hp0,hp1,hq0,hq1,hr]
  have hz : 0 < s := by
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hp.mem_iff.mpr (by simp : (0,[p,q]) ∈ _))
    have hh := (hG.1 i).1
    simpa only [hi] using hh
  refine ⟨?_,hG.2.1,?_⟩
  · intro i
    have hm : (query mode G).vertices.get i ∈ rows mode p q r t tail := by
      rw [← he]
      exact List.get_mem _ _
    generalize (query mode G).vertices.get i = row at hm ⊢
    have htail : ∀ row ∈ tail, row.1 < s ∧ row.2.length = arity row.1 := by
      intro v hv
      have hvG : v ∈ G.vertices := hp.mem_iff.mpr (by simp [hv])
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hvG
      rw [← hj]
      exact hG.1 j
    unfold rows at hm
    split at hm <;> (try split at hm) <;>
      simp only [List.mem_cons] at hm <;>
      rcases hm with rfl | rfl | hm
    all_goals first | exact htail _ hm | exact ⟨hz,by simp [hzero]⟩
  · have hends := (hp.map Prod.snd).flatten
    have ho : G.endpoints.Perm ([p,q,r,t] ++ (tail.map Prod.snd).flatten) := by
      simpa [RawClosedNetwork.endpoints,List.append_assoc] using hends
    have hnew : (query mode G).endpoints.Perm
        ([p,q,r,t] ++ (tail.map Prod.snd).flatten) := by
      change (((query mode G).vertices.map Prod.snd).flatten).Perm _
      rw [he]
      exact rows_endpoints mode p q r t tail
    exact hnew.trans (ho.symm.trans hG.2.2)

end Paper2.BellReduction.RawPairing
