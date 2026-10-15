import Paper2.BellReduction.RawChargeLanguage
import Paper2.BellReduction.NativeSmoothing.Compile

/-! Label-level removal of the distinguished extension. Original duplicate
labels and nullary rows remain separate; only their literal indices shift. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.BellReduction
open Complexity ExactInput Tractable Problem RawNative RelativeEO

 theorem tagged_table_succ (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (i : ℕ) (xs : List Bool) :
    languageTable (tagged L g) (i+1) xs = languageTable L i xs := by
  by_cases hi : i < L.count
  · have hi' : i+1 < (tagged L g).count := by rw [tagged_count]; omega
    have hs : (tagged L g).signature ⟨i+1,hi'⟩ = L.signature ⟨i,hi⟩ :=
      eq_of_heq (Sigma.mk.inj (tagged_succ L g ⟨i,hi⟩)).2
    simp only [languageTable,dif_pos hi,dif_pos hi',tagged_arity_succ]
    split <;> simp only [hs]
  · have hi' : ¬ i+1 < (tagged L g).count := by rw [tagged_count]; omega
    simp only [languageTable,dif_neg hi,dif_neg hi']

 theorem tagged_tables_agree (L : Language) {n m : ℕ}
    (f : Signature AlgebraicComplex n) (g : Signature AlgebraicComplex m)
    (label : ℕ) (hl : label ≠ 0) (xs : List Bool) :
    languageTable (tagged L f) label xs = languageTable (tagged L g) label xs := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  rw [tagged_table_succ,tagged_table_succ]

 theorem tagged_table_binary (L : Language) (g : Signature AlgebraicComplex 2)
    (a b : Bool) : languageTable (tagged L g) 0 [a,b] = g ![a,b] := by
  simpa using languageTable_literal (tagged L g) ⟨0,by simp⟩ g (tagged_zero L g) ![a,b]

 def unmark (G : RawClosedNetwork) : RawClosedNetwork where
  vertices := G.vertices.map (fun v => (v.1-1,v.2))
  edges := G.edges

 theorem unmark_wellFormed (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (G : Instance (tagged L g)) (hz : RawOccurrence.markedCount G.val.vertices = 0) :
    (unmark G.val).WellFormed L.count 1 L.arity := by
  have hnone : ∀ row ∈ G.val.vertices, row.1 ≠ 0 := by
    have hf := List.length_eq_zero_iff.mp hz
    intro row hr he
    have hh : row ∈ G.val.vertices.filter (fun v => v.1 == 0) := by simp [hr,he]
    rw [hf] at hh
    exact List.not_mem_nil hh
  refine ⟨?_,G.property.2.1,?_⟩
  · intro i
    have hm := List.get_mem (unmark G.val).vertices i
    obtain ⟨row,hr,he⟩ := List.mem_map.mp hm
    rw [← he]
    have hn := hnone row hr
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hr
    have hh := G.property.1 j
    rw [hj] at hh
    obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [ha] at hh ⊢
    simp only [Nat.add_sub_cancel,tagged_arity_succ,tagged_count] at hh ⊢
    exact ⟨by omega,hh.2⟩
  · have he : (unmark G.val).endpoints = G.val.endpoints := by
      simp [unmark,RawClosedNetwork.endpoints,List.map_map,Function.comp_def]
    rw [he]
    exact G.property.2.2

/-- Dropping the absent designated label preserves the exact raw value. -/
theorem unmark_value (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (G : Instance (tagged L g)) (hz : RawOccurrence.markedCount G.val.vertices = 0) :
    evaluate (languageTable (tagged L g)) G.val = evaluate (languageTable L) (unmark G.val) := by
  have hnone : ∀ row ∈ G.val.vertices, row.1 ≠ 0 := by
    have hf := List.length_eq_zero_iff.mp hz
    intro row hr he
    have hh : row ∈ G.val.vertices.filter (fun v => v.1 == 0) := by simp [hr,he]
    rw [hf] at hh
    exact List.not_mem_nil hh
  unfold evaluate
  apply Finset.sum_congr rfl
  intro z _
  change (G.val.vertices.map (rowValue (languageTable (tagged L g)) z)).prod =
    ((G.val.vertices.map (fun v => (v.1-1,v.2))).map (rowValue (languageTable L) z)).prod
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro row hr
  obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero (hnone row hr)
  simp only [rowValue,Function.comp_apply,ha,Nat.succ_sub_one,tagged_table_succ]

end Paper2.BellReduction
