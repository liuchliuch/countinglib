import Paper2.BellReduction.OriginalQueries
import Paper2.BellReduction.RawDisjointUnion

/-! Residual single-occurrence branches on original serialized instances.
A nonzero Y witness is a fixed closed instance; disjoint union turns each
one-Y input into a two-Y input. Without such a witness the branch is zero. -/
namespace Paper2.BellReduction.OriginalQueries
open Complexity ExactInput Tractable Problem RawOccurrence RawNative RelativeEO
open NativeSmoothing NativeSmoothing.Surgery Bell

 theorem one_i (L : Language) (hF : HighCharge L.family)
    (G : Instance (tagged L (bellTable false false))) (hc : markedCount G.val.vertices = 1) :
    value .nativeX (tagged L (bellTable false false)) G = 0 := by
  obtain ⟨ends,tail,hpop⟩ := popMarked_exists (vs := G.val.vertices) (by omega)
  have hp := popMarked_perm hpop
  have hlen : ends.length = 2 := by
    have hm : (0,ends) ∈ G.val.vertices := hp.mem_iff.mpr (by simp)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
    have hh := (G.property.1 i).2
    rw [hi] at hh
    exact hh.trans (tagged_arity_zero L _)
  obtain ⟨p,q,rfl⟩ := List.length_eq_two.mp hlen
  have hcount := popMarked_count hpop
  have hz : markedCount tail = 0 := by omega
  have hnone : ∀ row ∈ tail, row.1 ≠ 0 := by
    have hf := List.length_eq_zero_iff.mp hz
    intro row hr he
    have hm : row ∈ tail.filter (fun v => v.1 == 0) := by simp [hr,he]
    rw [hf] at hm
    exact List.not_mem_nil hm
  rw [← evaluate_language,← evaluate_eq_raw _ _ G.property,Choice.evaluate_perm _ _ hp]
  apply RawBell.one_i
  · have hh := (hp.map Prod.snd).flatten
    have he : G.val.endpoints.Perm ([p,q] ++ (tail.map Prod.snd).flatten) := by
      simpa [RawClosedNetwork.endpoints,List.append_assoc] using hh
    exact he.symm.trans (G.property.2.2.trans (by rw [expectedEndpoints_eq]))
  · intro a b
    rw [tagged_table_binary]
    rfl
  · intro row hr xs hn
    exact RawCharge.tagged_language_charge L _ hF row.1 (hnone row hr) xs hn

 noncomputable def witnessUnion (L : Language) (G W : Instance (tagged L (bellTable true true))) :
    Instance (tagged L (bellTable true true)) :=
  ⟨RawDisjointUnion.union G.val W.val,RawDisjointUnion.union_wellFormed G.property W.property⟩

 theorem witnessUnion_count (L : Language) (G W : Instance (tagged L (bellTable true true)))
    (hG : markedCount G.val.vertices = 1) (hW : markedCount W.val.vertices = 1) :
    markedCount (witnessUnion L G W).val.vertices = 2 := by
  change markedCount (RawDisjointUnion.union G.val W.val).vertices = _
  rw [RawDisjointUnion.union_count,hG,hW]

 theorem witnessUnion_value (L : Language) (G W : Instance (tagged L (bellTable true true))) :
    value .nativeX (tagged L (bellTable true true)) (witnessUnion L G W) =
      value .nativeX (tagged L (bellTable true true)) G *
        value .nativeX (tagged L (bellTable true true)) W := by
  rw [← evaluate_language,← evaluate_language,← evaluate_language]
  exact RawDisjointUnion.union_value _ G.property W.property

/-- Fixed nonzero one-Y witness gives two real original-language queries, with
no appeal to a possibly ill-formed punctured open graph. -/
theorem one_y_queries (L : Language) (W : Instance (tagged L (bellTable true true)))
    (hW : markedCount W.val.vertices = 1)
    (hne : value .nativeX (tagged L (bellTable true true)) W ≠ 0)
    (G : Instance (tagged L (bellTable true true))) (hG : markedCount G.val.vertices = 1) :
    value .nativeX (tagged L (bellTable true true)) G =
      (weightedQuery L (bellTable true true) (witnessUnion L G W) (witnessUnion_count L G W hG hW) 2 -
        weightedQuery L (bellTable true true) (witnessUnion L G W) (witnessUnion_count L G W hG hW) 1) /
          value .nativeX (tagged L (bellTable true true)) W := by
  apply (eq_div_iff hne).mpr
  rw [← two_y L (witnessUnion L G W) (witnessUnion_count L G W hG hW),witnessUnion_value]

/-- This is the exact zero alternative used when no fixed witness exists. -/
theorem one_y_zero_of_no_witness (L : Language)
    (h : ¬ ∃ W : Instance (tagged L (bellTable true true)),
      markedCount W.val.vertices = 1 ∧ value .nativeX (tagged L (bellTable true true)) W ≠ 0)
    (G : Instance (tagged L (bellTable true true))) (hG : markedCount G.val.vertices = 1) :
    value .nativeX (tagged L (bellTable true true)) G = 0 := by
  by_contra hn
  exact h ⟨G,hG,hn⟩

end Paper2.BellReduction.OriginalQueries
