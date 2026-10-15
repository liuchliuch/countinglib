import Paper2.FixedFieldOutput.OccurrenceReductions
import Paper2.Complexity.BellMachines.RawTripleCompile
import Paper2.Complexity.BellMachines.NaturalSubtraction
import Paper2.BellReduction.RawNativeSemantics

/-! Forget a discharged distinguished label by an actual row-label program.
Only literal integer labels change; all ordered endpoints, edge labels, loops
and nullary vertices survive. Input and output are the original graph codecs. -/
namespace Paper2.FixedFieldOutput.DropTag
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines BellMachines
open Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.RelativeEO
open Paper2.BellReduction.RawNative
noncomputable section

 def raw (G : RawClosedNetwork) : RawClosedNetwork where
  vertices := G.vertices.map (fun v => (v.1-1,v.2))
  edges := G.edges

 def rowComputes : Computes RawClosedNetwork.vertexEncoding RawClosedNetwork.vertexEncoding
    (fun v => (v.1-1,v.2)) :=
  recode (pairComputes
    ((pairComputes RawTriple.rowLabelComputes
      (constantComputes RawClosedNetwork.vertexEncoding encodingNatBool 1)).andThen naturalSubtraction)
    RawTriple.rowEndsComputes) id (fun _ => rfl) (fun _ => rfl)

 def rawComputes : Computes RawClosedNetwork.encoding RawClosedNetwork.encoding raw := by
  let rows := (pairComputes (constantComputes RawClosedNetwork.encoding encodingBoolBool false)
    RawTriple.verticesComputes).andThen
      (Lists.mapListComputes encodingBoolBool RawClosedNetwork.vertexEncoding RawClosedNetwork.vertexEncoding
        (fun _ v => (v.1-1,v.2))
        ((Wiring.secondComputes encodingBoolBool RawClosedNetwork.vertexEncoding).andThen rowComputes))
  exact recode (pairComputes rows RawTriple.edgesComputes) id (fun _ => rfl) (fun _ => rfl)

 theorem label_ne_zero (G : RawClosedNetwork) (h : occurrenceCount G = 0)
    (v : RawVertex) (hv : v ∈ G.vertices) : v.1 ≠ 0 := by
  intro hz
  have hempty : G.vertices.filter (fun v => v.1 == 0) = [] := List.length_eq_zero_iff.mp h
  have hm : v ∈ G.vertices.filter (fun v => v.1 == 0) := by simp [hv,hz]
  rw [hempty] at hm
  exact List.not_mem_nil hm

 theorem wellFormed (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (G : Instance (tagged L g)) (h : occurrenceCount G.val = 0) :
    (raw G.val).WellFormed L.count 1 L.arity := by
  refine ⟨?_,G.property.2.1,?_⟩
  · intro v
    have hm := List.get_mem (raw G.val).vertices v
    obtain ⟨r,hr,he⟩ := List.mem_map.mp hm
    rw [← he]
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
    have hv := G.property.1 i
    rw [hi] at hv
    have hn := label_ne_zero G.val h r hr
    have har : (tagged L g).arity r.1 = L.arity (r.1-1) := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ r.1 by omega)]
      exact tagged_arity_succ L g (r.1-1)
    refine ⟨?_,hv.2.trans har⟩
    have hc := tagged_count L g
    omega
  · simpa [raw,RawClosedNetwork.endpoints,List.map_map,Function.comp_def,
      RawClosedNetwork.expectedEndpoints] using G.property.2.2

 def input (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (G : TaggedInstance L g (fun k => k = 0)) : Instance L :=
  ⟨raw G.val.val,wellFormed L g G.val G.property⟩

 def computes (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n) :
    Computes (taggedEncoding L g (fun k => k = 0)) (inputEncoding L) (input L g) :=
  recode rawComputes (fun G => G.val.val) (fun _ => rfl) (fun _ => rfl)

 theorem table_succ (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (a : ℕ) (xs : List Bool) : languageTable (tagged L g) (a+1) xs = languageTable L a xs := by
  by_cases ha : a < L.count
  · have hat : a+1 < (tagged L g).count := by rw [tagged_count]; omega
    by_cases hx : xs.length = L.arity a
    · have hxt : xs.length = (tagged L g).arity (a+1) := hx
      simp only [languageTable,dif_pos ha,dif_pos hat,dif_pos hx,dif_pos hxt]
      have he := tagged_succ L g ⟨a,ha⟩
      have hf := eq_of_heq (Sigma.mk.inj_iff.mp he).2
      exact congrFun hf _
    · have hxt : ¬ xs.length = (tagged L g).arity (a+1) := hx
      simp only [languageTable,dif_pos ha,dif_pos hat,dif_neg hx,dif_neg hxt]
  · have hat : ¬ a+1 < (tagged L g).count := by rw [tagged_count]; omega
    simp only [languageTable,dif_neg ha,dif_neg hat]

 theorem value (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (G : TaggedInstance L g (fun k => k = 0)) :
    Problem.value .nativeX L (input L g G) = Problem.value .nativeX (tagged L g) G.val := by
  rw [← evaluate_language,← evaluate_language]
  change evaluate (languageTable L) (raw G.val.val) = evaluate (languageTable (tagged L g)) G.val.val
  unfold evaluate
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  change ((G.val.val.vertices.map (fun v => (v.1-1,v.2))).map (rowValue (languageTable L) z)) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro v hv
  have hn := label_ne_zero G.val.val G.property v hv
  change languageTable L (v.1-1) (v.2.map (readEnd z)) = languageTable (tagged L g) v.1 _
  conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ v.1 by omega)]
  exact (table_succ L g (v.1-1) _).symm

end
end Paper2.FixedFieldOutput.DropTag
