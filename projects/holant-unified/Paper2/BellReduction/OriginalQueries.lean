import Paper2.BellReduction.RawClosures

/-! Exact Bell closure identities whose query arguments are actual validated
instances of the original language. All closed-circle factors are explicit. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.BellReduction.OriginalQueries
open Complexity ExactInput Tractable Problem RawOccurrence RawNative RelativeEO
open NativeSmoothing NativeSmoothing.Surgery Bell

 theorem no_marked_tables (L : Language) {n m : ℕ}
    (f : Signature AlgebraicComplex n) (g : Signature AlgebraicComplex m)
    (G : RawClosedNetwork) (hz : markedCount G.vertices = 0) :
    evaluate (languageTable (tagged L f)) G = evaluate (languageTable (tagged L g)) G := by
  have hf := List.length_eq_zero_iff.mp hz
  have hn : ∀ row ∈ G.vertices, row.1 ≠ 0 := by
    intro row hr he
    have hh : row ∈ G.vertices.filter (fun v => v.1 == 0) := by simp [hr,he]
    rw [hf] at hh
    exact List.not_mem_nil hh
  unfold evaluate
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply List.map_congr_left
  intro row hr
  exact tagged_tables_agree L f g row.1 (hn row hr) _

 theorem native_table (L : Language) (a b : Bool) :
    languageTable (tagged L (bellTable true false)) 0 [a,b] = Signature.disequality a b := by
  rw [tagged_table_binary]
  change X a b = Signature.disequality a b
  rw [X_eq_disequality]

 noncomputable def weightedQuery (L : Language) (g : Signature AlgebraicComplex 2)
    (G : Instance (tagged L g)) (hc : markedCount G.val.vertices = 2) (mode : Fin 3) : AlgebraicComplex :=
  RawClosures.scalar (RawClosures.close mode G.val) *
    value .nativeX L (RawClosures.query L g G hc mode)

/-- Two sequential raw splices, with their circle flags, give an actual query
in L rather than an oracle call on a Bell-extended alphabet. -/
theorem weighted_query_value (L : Language) (g : Signature AlgebraicComplex 2)
    (G : Instance (tagged L g)) (hc : markedCount G.val.vertices = 2) (mode : Fin 3) :
    Choice.evaluate (languageTable (tagged L (bellTable true false))) G.val.edges.length
        (RawPairing.query mode G.val).vertices = weightedQuery L g G hc mode := by
  have hw := RawPairing.query_wellFormed G.property (tagged_arity_zero L g) (by omega) mode
  have hs := RawClosures.close_wellFormed G.property (tagged_arity_zero L g) (by omega) mode
  have hz : markedCount (RawClosures.close mode G.val).query.vertices = 0 := by
    rw [RawClosures.close_count G.property (tagged_arity_zero L g) (by omega) mode,hc]
  change Choice.evaluate _ (RawPairing.query mode G.val).edges.length _ = _
  rw [evaluate_eq_raw _ _ hw,RawClosures.close_value _ G.property
    (tagged_arity_zero L g) (by omega) mode (native_table L)]
  unfold weightedQuery
  congr 1
  rw [no_marked_tables L (bellTable true false) g _ hz,
    unmark_value L g ⟨_,hs⟩ hz]
  exact evaluate_language L (RawClosures.query L g G hc mode)

 theorem rest_no_mark {G : RawClosedNetwork} {p q r s : RawEndpoint} {tail : List RawVertex}
    (hp : G.vertices.Perm ((0,[p,q])::(0,[r,s])::tail))
    (hc : markedCount G.vertices = 2) : ∀ row ∈ tail, row.1 ≠ 0 := by
  have hcount := markedCount_perm hp
  simp only [markedCount_cons_zero] at hcount
  have hz : markedCount tail = 0 := by omega
  have hf := List.length_eq_zero_iff.mp hz
  intro row hr he
  have hm : row ∈ tail.filter (fun v => v.1 == 0) := by simp [hr,he]
  rw [hf] at hm
  exact List.not_mem_nil hm

 theorem value_as_choice (L : Language) (g : Signature AlgebraicComplex 2)
    (G : Instance (tagged L g)) {p q r s : RawEndpoint} {tail : List RawVertex}
    (hp : G.val.vertices.Perm ((0,[p,q])::(0,[r,s])::tail)) :
    value .nativeX (tagged L g) G = Choice.evaluate (languageTable (tagged L g))
      G.val.edges.length ((0,[p,q])::(0,[r,s])::tail) := by
  rw [← evaluate_language,← evaluate_eq_raw _ _ G.property]
  exact Choice.evaluate_perm _ _ hp

/-- The two ordered Y occurrences are removed by two original-language queries,
with the correct sign and every zero/one/two-circle multiplier. -/
theorem two_y (L : Language) (G : Instance (tagged L (bellTable true true)))
    (hc : markedCount G.val.vertices = 2) :
    value .nativeX (tagged L (bellTable true true)) G =
      weightedQuery L (bellTable true true) G hc 2 - weightedQuery L (bellTable true true) G hc 1 := by
  obtain ⟨p,q,r,s,tail,hp,hp0,hp1,hq0,hq1,hr⟩ :=
    RawPairing.selected_two G.property (tagged_arity_zero L _) (by omega)
  rw [value_as_choice L _ G hp,← weighted_query_value,← weighted_query_value]
  simp only [RawPairing.query,hp0,hp1,hq0,hq1,hr,RawPairing.rows,Fin.val_zero,
    Fin.val_one,Fin.reduceFinMk,ite_true,ite_false,OfNat.ofNat_ne_zero,one_ne_zero]
  apply RawBell.two_y
  · intro a b
    rw [tagged_table_binary]
    rfl
  · intro a b
    rw [tagged_table_binary]
    rfl
  · intro row hm xs
    exact tagged_tables_agree L _ _ row.1 (rest_no_mark hp hc row hm) xs

/-- The three-query I identity follows from the original ambient high-charge
language, with no supplied boundary tensor or promised open-graph shape. -/
theorem two_i (L : Language) (hF : HighCharge L.family)
    (G : Instance (tagged L (bellTable false false))) (hc : markedCount G.val.vertices = 2) :
    (2 : AlgebraicComplex) * value .nativeX (tagged L (bellTable false false)) G =
      weightedQuery L (bellTable false false) G hc 1 + weightedQuery L (bellTable false false) G hc 2 -
        weightedQuery L (bellTable false false) G hc 0 := by
  obtain ⟨p,q,r,s,tail,hp,hp0,hp1,hq0,hq1,hr⟩ :=
    RawPairing.selected_two G.property (tagged_arity_zero L _) (by omega)
  rw [value_as_choice L _ G hp,← weighted_query_value,← weighted_query_value,← weighted_query_value]
  simp only [RawPairing.query,hp0,hp1,hq0,hq1,hr,RawPairing.rows,Fin.val_zero,
    Fin.val_one,Fin.reduceFinMk,ite_true,ite_false,OfNat.ofNat_ne_zero,one_ne_zero]
  apply RawBell.two_i
  · have hh := (hp.map Prod.snd).flatten
    have he : G.val.endpoints.Perm ([p,q,r,s] ++ (tail.map Prod.snd).flatten) := by
      simpa [RawClosedNetwork.endpoints,List.append_assoc] using hh
    exact he.symm.trans (G.property.2.2.trans (by rw [expectedEndpoints_eq]))
  · intro a b
    rw [tagged_table_binary]
    rfl
  · intro a b
    rw [tagged_table_binary]
    rfl
  · intro row hm xs
    exact tagged_tables_agree L _ _ row.1 (rest_no_mark hp hc row hm) xs
  · intro row hm xs hn
    exact RawCharge.tagged_language_charge L _ hF row.1 (rest_no_mark hp hc row hm) xs hn

end Paper2.BellReduction.OriginalQueries
