import Paper2.Certificates.Q8ActualDeckCore

namespace Paper2.Certificates.Q8.Atlas
open ReedMuller

def pairIndex : Port → Port → PairIndex := ![![0, 0, 1, 2, 3, 4, 5, 6], ![0, 0, 7, 8, 9, 10, 11, 12], ![1, 7, 0, 13, 14, 15, 16, 17], ![2, 8, 13, 0, 18, 19, 20, 21], ![3, 9, 14, 18, 0, 22, 23, 24], ![4, 10, 15, 19, 22, 0, 25, 26], ![5, 11, 16, 20, 23, 25, 0, 27], ![6, 12, 17, 21, 24, 26, 27, 0]]

theorem pairIndex_symmetric (p q : Port) : pairIndex p q = pairIndex q p := by
  revert p q
  decide +kernel

theorem pairIndex_endpoints (p q : Port) (h : p ≠ q) :
    deleted (pairIndex p q) = (p,q) ∨ deleted (pairIndex p q) = (q,p) := by
  revert p q
  decide +kernel

theorem TranslationAt.swap {p q : Port} {x : Word} (h : TranslationAt p q x) :
    TranslationAt q p x := by
  intro v hvq hvp
  rw [port_xor_comm q p]
  exact h v hvp hvq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem translationAt_iff_0 (q : Port) (x : Word) (h : 0 ≠ q) :
    TranslationAt 0 q x ↔ TranslationTransversal (residualWord 0 q x) := by
  revert q x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem translationAt_iff_1 (q : Port) (x : Word) (h : 1 ≠ q) :
    TranslationAt 1 q x ↔ TranslationTransversal (residualWord 1 q x) := by
  revert q x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem translationAt_iff_2 (q : Port) (x : Word) (h : 2 ≠ q) :
    TranslationAt 2 q x ↔ TranslationTransversal (residualWord 2 q x) := by
  revert q x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem translationAt_iff_3 (q : Port) (x : Word) (h : 3 ≠ q) :
    TranslationAt 3 q x ↔ TranslationTransversal (residualWord 3 q x) := by
  revert q x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem translationAt_iff_4 (q : Port) (x : Word) (h : 4 ≠ q) :
    TranslationAt 4 q x ↔ TranslationTransversal (residualWord 4 q x) := by
  revert q x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem translationAt_iff_5 (q : Port) (x : Word) (h : 5 ≠ q) :
    TranslationAt 5 q x ↔ TranslationTransversal (residualWord 5 q x) := by
  revert q x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem translationAt_iff_6 (q : Port) (x : Word) (h : 6 ≠ q) :
    TranslationAt 6 q x ↔ TranslationTransversal (residualWord 6 q x) := by
  revert q x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem translationAt_iff_7 (q : Port) (x : Word) (h : 7 ≠ q) :
    TranslationAt 7 q x ↔ TranslationTransversal (residualWord 7 q x) := by
  revert q x
  decide +kernel

theorem translationAt_iff_transversal (p q : Port) (x : Word) (h : p ≠ q) :
    TranslationAt p q x ↔ TranslationTransversal (residualWord p q x) := by
  fin_cases p
  · exact translationAt_iff_0 q x h
  · exact translationAt_iff_1 q x h
  · exact translationAt_iff_2 q x h
  · exact translationAt_iff_3 q x h
  · exact translationAt_iff_4 q x h
  · exact translationAt_iff_5 q x h
  · exact translationAt_iff_6 q x h
  · exact translationAt_iff_7 q x h

theorem labeled_weight (p : Equiv.Perm Port) (x : Word) :
    weight (fun v => x (p v)) = weight x := by
  unfold weight
  exact Fintype.sum_equiv p _ _ (fun _ => rfl)

end Paper2.Certificates.Q8.Atlas
