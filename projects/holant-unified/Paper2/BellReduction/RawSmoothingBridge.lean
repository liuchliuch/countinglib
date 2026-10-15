import Paper2.Complexity.BellMachines.RawSmoothing
import Paper2.BellReduction.RawTripleBridge
import Paper2.BellReduction.NativeSmoothing.Compile

/-! The finite-list smoother and the indexed incidence smoother agree on
original native-X input bytes, with exactly the same retained row ordering. -/
namespace Paper2.BellReduction
open Complexity RawOccurrence NativeSmoothing NativeSmoothing.Surgery
open RawTripleBridge

 theorem popMarked_index {vs : List RawVertex} {p : List RawEndpoint} {rest : List RawVertex}
    (h : popMarked vs = some (p,rest)) :
    vs[vs.findIdx (fun v => v.1 == 0)]? = some (0,p) ∧
      vs.eraseIdx (vs.findIdx (fun v => v.1 == 0)) = rest := by
  induction vs generalizing rest with
  | nil => simp [popMarked] at h
  | cons v vs ih =>
    rcases v with ⟨a,q⟩
    by_cases ha : a = 0
    · subst a
      simp only [popMarked,ite_true,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      simp [List.findIdx_cons]
    · cases hp : popMarked vs with
      | none => simp [popMarked,ha,hp] at h
      | some r =>
        rcases r with ⟨q',tail⟩
        simp only [popMarked,ha,ite_false,hp,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simpa [List.findIdx_cons,ha] using ih hp

 theorem native_edges_erase {G : RawClosedNetwork} {s : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s 1 arity) (e : ℕ) (he : e < G.edges.length) :
    G.edges.eraseIdx e = List.replicate (G.edges.length-1) 0 := by
  apply List.eq_replicate_iff.mpr
  refine ⟨List.length_eraseIdx_of_lt he,?_⟩
  intro a ha
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((List.eraseIdx_sublist G.edges e).subset ha)
  have hh := hG.2.1 i
  rw [hi] at hh
  omega

/-- Agreement on every original valid native graph, including no-marker input.
The Boolean active test has no semantic table comparison. -/
theorem rawSmoothing_eq_compile {G : RawClosedNetwork} {s : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s 1 arity) (hzero : arity 0 = 2) :
    BellMachines.RawSmoothing.compile G = Smoothing.compile 0 G := by
  cases hp : popMarked G.vertices with
  | none =>
    have hc := (popMarked_none G.vertices).mp hp
    have hf : marked G.vertices = [] := List.length_eq_zero_iff.mp hc
    have hs : BellMachines.RawSmoothing.row G = (0,[]) := by
      change (marked G.vertices).getD 0 (0,[]) = _
      rw [hf]
      rfl
    have hnone : ∀ row ∈ G.vertices, (row.1 == 0) = false := by
      intro row hr
      have he := List.filter_eq_nil_iff.mp hf row hr
      simpa using he
    have hi := List.findIdx_eq_length.mpr hnone
    simp [BellMachines.RawSmoothing.compile,BellMachines.RawSmoothing.active,hs,
      Smoothing.compile,hi]
  | some a =>
    rcases a with ⟨ends,rest⟩
    have hm := popMarked_marked hp
    have hs : BellMachines.RawSmoothing.row G = (0,ends) := by
      change (marked G.vertices).getD 0 (0,[]) = _
      rw [hm]
      rfl
    have he : ends.length = 2 := by
      have hv : (0,ends) ∈ G.vertices := (popMarked_perm hp).mem_iff.mpr (by simp)
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hv
      have hh := (hG.1 i).2
      rw [hi] at hh
      exact hh.trans hzero
    obtain ⟨p,q,rfl⟩ := List.length_eq_two.mp he
    have hind := popMarked_index hp
    have hremain : BellMachines.RawSmoothing.remaining G = rest := by
      unfold BellMachines.RawSmoothing.remaining
      rw [hs]
      exact (popMarked_filter hp (marked_nodup hG hzero)).symm
    have hbound (t : RawEndpoint) (ht : t ∈ [p,q]) : t.1 < G.edges.length :=
      endpoint_bound hG ((popMarked_perm hp).mem_iff.mpr
        (by simp : (0,[p,q]) ∈ (0,[p,q])::rest)) ht
    have hbP := hbound p (by simp)
    have hbQ := hbound q (by simp)
    have hf : BellMachines.RawSmoothing.first G = p := by
      simp [BellMachines.RawSmoothing.first,hs]
    have hq : BellMachines.RawSmoothing.second G = q := by
      simp [BellMachines.RawSmoothing.second,hs]
    have hactive : BellMachines.RawSmoothing.active G = true := by
      simp [BellMachines.RawSmoothing.active,hs]
    unfold Smoothing.compile
    dsimp only
    rw [hind.1]
    simp only [Option.map_some]
    unfold BellMachines.RawSmoothing.compile
    rw [hactive]
    simp only [ite_true]
    by_cases heq : p.1 = q.1
    · simp [Smoothing.smoothAt,heq,BellMachines.RawSmoothing.circle,hf,hq,
        BellMachines.RawSmoothing.query,hremain,BellMachines.RawSmoothing.remap,
        Smoothing.emit,hind.2,native_edges_erase hG p.1 hbP,native_edges_erase hG q.1 hbQ]
    · simp [Smoothing.smoothAt,heq,BellMachines.RawSmoothing.circle,hf,hq,
        BellMachines.RawSmoothing.query,hremain,BellMachines.RawSmoothing.remap,
        Smoothing.emit,hind.2,native_edges_erase hG q.1 hbQ]

end Paper2.BellReduction
