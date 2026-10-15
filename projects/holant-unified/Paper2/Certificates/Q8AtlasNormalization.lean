import Paper2.Certificates.Q8AtlasRelabel

/-! Fifteen literal initial matching normalizations. Every finite table is
checked for inverses, unordered endpoint transport, and mate conjugacy. -/
namespace Paper2.Certificates.Q8.Atlas

def normalizationPorts : Choice → Port → Port := ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 6, 5, 7], ![0, 1, 2, 3, 4, 7, 5, 6], ![0, 1, 2, 4, 3, 5, 6, 7], ![0, 1, 2, 4, 3, 6, 5, 7], ![0, 1, 2, 4, 3, 7, 5, 6], ![0, 1, 2, 5, 3, 4, 6, 7], ![0, 1, 2, 5, 3, 6, 4, 7], ![0, 1, 2, 5, 3, 7, 4, 6], ![0, 1, 2, 6, 3, 4, 5, 7], ![0, 1, 2, 6, 3, 5, 4, 7], ![0, 1, 2, 6, 3, 7, 4, 5], ![0, 1, 2, 7, 3, 4, 5, 6], ![0, 1, 2, 7, 3, 5, 4, 6], ![0, 1, 2, 7, 3, 6, 4, 5]]
def normalizationPortsInv : Choice → Port → Port := ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 6, 5, 7], ![0, 1, 2, 3, 4, 6, 7, 5], ![0, 1, 2, 4, 3, 5, 6, 7], ![0, 1, 2, 4, 3, 6, 5, 7], ![0, 1, 2, 4, 3, 6, 7, 5], ![0, 1, 2, 4, 5, 3, 6, 7], ![0, 1, 2, 4, 6, 3, 5, 7], ![0, 1, 2, 4, 6, 3, 7, 5], ![0, 1, 2, 4, 5, 6, 3, 7], ![0, 1, 2, 4, 6, 5, 3, 7], ![0, 1, 2, 4, 6, 7, 3, 5], ![0, 1, 2, 4, 5, 6, 7, 3], ![0, 1, 2, 4, 6, 5, 7, 3], ![0, 1, 2, 4, 6, 7, 5, 3]]
def normalizationPairs : Choice → PairIndex → PairIndex := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], ![0, 1, 2, 3, 5, 4, 6, 7, 8, 9, 11, 10, 12, 13, 14, 16, 15, 17, 18, 20, 19, 21, 23, 22, 24, 25, 27, 26], ![0, 1, 2, 3, 6, 4, 5, 7, 8, 9, 12, 10, 11, 13, 14, 17, 15, 16, 18, 21, 19, 20, 24, 22, 23, 26, 27, 25], ![0, 1, 3, 2, 4, 5, 6, 7, 9, 8, 10, 11, 12, 14, 13, 15, 16, 17, 18, 22, 23, 24, 19, 20, 21, 25, 26, 27], ![0, 1, 3, 2, 5, 4, 6, 7, 9, 8, 11, 10, 12, 14, 13, 16, 15, 17, 18, 23, 22, 24, 20, 19, 21, 25, 27, 26], ![0, 1, 3, 2, 6, 4, 5, 7, 9, 8, 12, 10, 11, 14, 13, 17, 15, 16, 18, 24, 22, 23, 21, 19, 20, 26, 27, 25], ![0, 1, 4, 2, 3, 5, 6, 7, 10, 8, 9, 11, 12, 15, 13, 14, 16, 17, 19, 22, 25, 26, 18, 20, 21, 23, 24, 27], ![0, 1, 4, 2, 5, 3, 6, 7, 10, 8, 11, 9, 12, 15, 13, 16, 14, 17, 19, 25, 22, 26, 20, 18, 21, 23, 27, 24], ![0, 1, 4, 2, 6, 3, 5, 7, 10, 8, 12, 9, 11, 15, 13, 17, 14, 16, 19, 26, 22, 25, 21, 18, 20, 24, 27, 23], ![0, 1, 5, 2, 3, 4, 6, 7, 11, 8, 9, 10, 12, 16, 13, 14, 15, 17, 20, 23, 25, 27, 18, 19, 21, 22, 24, 26], ![0, 1, 5, 2, 4, 3, 6, 7, 11, 8, 10, 9, 12, 16, 13, 15, 14, 17, 20, 25, 23, 27, 19, 18, 21, 22, 26, 24], ![0, 1, 5, 2, 6, 3, 4, 7, 11, 8, 12, 9, 10, 16, 13, 17, 14, 15, 20, 27, 23, 25, 21, 18, 19, 24, 26, 22], ![0, 1, 6, 2, 3, 4, 5, 7, 12, 8, 9, 10, 11, 17, 13, 14, 15, 16, 21, 24, 26, 27, 18, 19, 20, 22, 23, 25], ![0, 1, 6, 2, 4, 3, 5, 7, 12, 8, 10, 9, 11, 17, 13, 15, 14, 16, 21, 26, 24, 27, 19, 18, 20, 22, 25, 23], ![0, 1, 6, 2, 5, 3, 4, 7, 12, 8, 11, 9, 10, 17, 13, 16, 14, 15, 21, 27, 24, 26, 20, 18, 19, 23, 25, 22]]
def normalizationPairsInv : Choice → PairIndex → PairIndex := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], ![0, 1, 2, 3, 5, 4, 6, 7, 8, 9, 11, 10, 12, 13, 14, 16, 15, 17, 18, 20, 19, 21, 23, 22, 24, 25, 27, 26], ![0, 1, 2, 3, 5, 6, 4, 7, 8, 9, 11, 12, 10, 13, 14, 16, 17, 15, 18, 20, 21, 19, 23, 24, 22, 27, 25, 26], ![0, 1, 3, 2, 4, 5, 6, 7, 9, 8, 10, 11, 12, 14, 13, 15, 16, 17, 18, 22, 23, 24, 19, 20, 21, 25, 26, 27], ![0, 1, 3, 2, 5, 4, 6, 7, 9, 8, 11, 10, 12, 14, 13, 16, 15, 17, 18, 23, 22, 24, 20, 19, 21, 25, 27, 26], ![0, 1, 3, 2, 5, 6, 4, 7, 9, 8, 11, 12, 10, 14, 13, 16, 17, 15, 18, 23, 24, 22, 20, 21, 19, 27, 25, 26], ![0, 1, 3, 4, 2, 5, 6, 7, 9, 10, 8, 11, 12, 14, 15, 13, 16, 17, 22, 18, 23, 24, 19, 25, 26, 20, 21, 27], ![0, 1, 3, 5, 2, 4, 6, 7, 9, 11, 8, 10, 12, 14, 16, 13, 15, 17, 23, 18, 22, 24, 20, 25, 27, 19, 21, 26], ![0, 1, 3, 5, 2, 6, 4, 7, 9, 11, 8, 12, 10, 14, 16, 13, 17, 15, 23, 18, 24, 22, 20, 27, 25, 21, 19, 26], ![0, 1, 3, 4, 5, 2, 6, 7, 9, 10, 11, 8, 12, 14, 15, 16, 13, 17, 22, 23, 18, 24, 25, 19, 26, 20, 27, 21], ![0, 1, 3, 5, 4, 2, 6, 7, 9, 11, 10, 8, 12, 14, 16, 15, 13, 17, 23, 22, 18, 24, 25, 20, 27, 19, 26, 21], ![0, 1, 3, 5, 6, 2, 4, 7, 9, 11, 12, 8, 10, 14, 16, 17, 13, 15, 23, 24, 18, 22, 27, 20, 25, 21, 26, 19], ![0, 1, 3, 4, 5, 6, 2, 7, 9, 10, 11, 12, 8, 14, 15, 16, 17, 13, 22, 23, 24, 18, 25, 26, 19, 27, 20, 21], ![0, 1, 3, 5, 4, 6, 2, 7, 9, 11, 10, 12, 8, 14, 16, 15, 17, 13, 23, 22, 24, 18, 25, 27, 20, 26, 19, 21], ![0, 1, 3, 5, 6, 4, 2, 7, 9, 11, 12, 10, 8, 14, 16, 17, 15, 13, 23, 24, 22, 18, 27, 25, 20, 26, 21, 19]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem normalization_inverses (k : Choice) :
    (∀ v, normalizationPortsInv k (normalizationPorts k v) = v) ∧
    (∀ v, normalizationPorts k (normalizationPortsInv k v) = v) ∧
    (∀ d, normalizationPairsInv k (normalizationPairs k d) = d) ∧
    (∀ d, normalizationPairs k (normalizationPairsInv k d) = d) := by
  revert k
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem normalization_endpoints (k : Choice) (d : PairIndex) :
    (normalizationPorts k (deleted d).1 = (deleted (normalizationPairs k d)).1 ∧
      normalizationPorts k (deleted d).2 = (deleted (normalizationPairs k d)).2) ∨
    (normalizationPorts k (deleted d).1 = (deleted (normalizationPairs k d)).2 ∧
      normalizationPorts k (deleted d).2 = (deleted (normalizationPairs k d)).1) := by
  revert k d
  decide +kernel

def normalization (k : Choice) : Relabeling where
  ports := ⟨normalizationPorts k,normalizationPortsInv k,
    (normalization_inverses k).1,(normalization_inverses k).2.1⟩
  pairs := ⟨normalizationPairs k,normalizationPairsInv k,
    (normalization_inverses k).2.2.1,(normalization_inverses k).2.2.2⟩
  endpoints := normalization_endpoints k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem normalization_root (k : Choice) :
    normalizationPairs k 0 = 0 ∧
    ∀ v, normalizationPortsInv k (fullMate 0 k (normalizationPorts k v)) = fullMate 0 0 v := by
  revert k
  decide +kernel

theorem normalization_family_root (M : (d : PairIndex) → Matching d) (k : Choice)
    (hk : (M 0).extend = fullMate 0 k) :
    ((normalization k).family M 0).extend = fullMate 0 0 := by
  funext v
  rw [Relabeling.extend_family]
  change normalizationPortsInv k ((M (normalizationPairs k 0)).extend (normalizationPorts k v)) = _
  rw [(normalization_root k).1,hk]
  exact (normalization_root k).2 v

end Paper2.Certificates.Q8.Atlas
