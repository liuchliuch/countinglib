import Paper2.Certificates.Q6Encoding

/-! Literal loop and two-copy hypotheses of Appendix A, together with the
complete 24 signed rows. Rows are in the upstream Python lexicographic triple
order; their free roots are compacted in increasing absolute-root order. -/
namespace Paper2.Certificates.Q6

structure LoopSpec where
  first : Port
  second : Port
  residual : Fin 4 → Port

def loopSpecs : Fin 15 → LoopSpec :=
  ![⟨0,1,![2, 3, 4, 5]⟩, ⟨0,2,![1, 3, 4, 5]⟩, ⟨0,3,![1, 2, 4, 5]⟩, ⟨0,4,![1, 2, 3, 5]⟩, ⟨0,5,![1, 2, 3, 4]⟩, ⟨1,2,![0, 3, 4, 5]⟩, ⟨1,3,![0, 2, 4, 5]⟩, ⟨1,4,![0, 2, 3, 5]⟩, ⟨1,5,![0, 2, 3, 4]⟩, ⟨2,3,![0, 1, 4, 5]⟩, ⟨2,4,![0, 1, 3, 5]⟩, ⟨2,5,![0, 1, 3, 4]⟩, ⟨3,4,![0, 1, 2, 5]⟩, ⟨3,5,![0, 1, 2, 4]⟩, ⟨4,5,![0, 1, 2, 3]⟩]

def loopChosen (s : LoopSpec) (e : Fin 6) : PortSet :=
  (Finset.univ.filter (fun j : Fin 4 => eoWords e j = true)).image s.residual

def loopMasks (s : LoopSpec) (e : Fin 6) : ℕ × ℕ :=
  (mask (insert s.first (loopChosen s e)), mask (insert s.second (loopChosen s e)))

/-- The manuscript's L_ij, in W₄ order, not the reverse Python loop order. -/
def loopArray {K : Type*} [AddMonoid K] (q : Fin 20 → K) (s : LoopSpec) : Fin 6 → K :=
  fun e => coefficient q (loopMasks s e).1 + coefficient q (loopMasks s e).2

def loopCoordinatePairs : Fin 15 → Fin 6 → Fin 20 × Fin 20 :=
  ![![(9,15), (8,14), (7,13), (6,12), (5,11), (4,10)], ![(9,18), (8,17), (7,16), (3,12), (2,11), (1,10)], ![(9,19), (6,17), (5,16), (3,14), (2,13), (0,10)], ![(8,19), (6,18), (4,16), (3,15), (1,13), (0,11)], ![(7,19), (5,18), (4,17), (2,15), (1,14), (0,12)], ![(15,18), (14,17), (13,16), (3,6), (2,5), (1,4)], ![(15,19), (12,17), (11,16), (3,8), (2,7), (0,4)], ![(14,19), (12,18), (10,16), (3,9), (1,7), (0,5)], ![(13,19), (11,18), (10,17), (2,9), (1,8), (0,6)], ![(18,19), (12,14), (11,13), (6,8), (5,7), (0,1)], ![(17,19), (12,15), (10,13), (6,9), (4,7), (0,2)], ![(16,19), (11,15), (10,14), (5,9), (4,8), (0,3)], ![(17,18), (14,15), (10,11), (8,9), (4,5), (1,2)], ![(16,18), (13,15), (10,12), (7,9), (4,6), (1,3)], ![(16,17), (13,14), (11,12), (7,8), (5,6), (2,3)]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem loop_specs_valid (i : Fin 15) :
    (loopSpecs i).first < (loopSpecs i).second ∧
    StrictMono (loopSpecs i).residual ∧
    Finset.univ.image (loopSpecs i).residual =
      Finset.univ \ {(loopSpecs i).first,(loopSpecs i).second} := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem loop_pairs_complete (p q : Port) (h : p < q) :
    ∃ i : Fin 15, (loopSpecs i).first = p ∧ (loopSpecs i).second = q := by
  revert p q
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem loop_masks_correct (i : Fin 15) (e : Fin 6) :
    loopMasks (loopSpecs i) e =
      (tripleMasks (loopCoordinatePairs i e).1, tripleMasks (loopCoordinatePairs i e).2) := by
  revert i e
  decide +kernel

theorem loopArray_coordinates {K : Type*} [AddMonoid K] (q : Fin 20 → K)
    (i : Fin 15) (e : Fin 6) :
    loopArray q (loopSpecs i) e = q (loopCoordinatePairs i e).1 + q (loopCoordinatePairs i e).2 := by
  unfold loopArray
  rw [loop_masks_correct]
  simp only [coefficient_at_triple]

/-- Exactly the validity conditions for an oriented four-wire bijection.
Only its restriction to the internal ports is used by the array. -/
def ValidCardSpec (s : CardSpec) : Prop :=
  s.left0 < s.left1 ∧ s.right0 < s.right1 ∧ Function.Bijective s.wiring ∧
    (internalLeft s).image s.wiring = internalRight s

def AllLoopSafe {K : Type*} [CommRing K] (q : Fin 20 → K) : Prop :=
  ∀ i : Fin 15, NecessarySafe (loopArray q (loopSpecs i))

def AllTwoCopySafe {K : Type*} [CommRing K] (q : Fin 20 → K) (t : K) : Prop :=
  ∀ s : CardSpec, ValidCardSpec s → NecessarySafe (twoCopyArray q t s)

/-- The complete official signed-row list, with at most eight free parameters. -/
def fullOrbit {K : Type*} [Ring K] (u : Fin 8 → K) : Fin 24 → Fin 20 → K :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, u 0, u 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, u 0, -u 0, u 1, -u 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, u 0, u 1, u 2, u 3, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, u 0, u 0, 0, -u 0, u 0, 0, -u 0, -u 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, u 0, u 0, 0, -u 0, u 1, 0, -u 1, -u 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, u 0, u 1, 0, -u 1, u 2, 0, -u 2, u 3, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, u 0, u 1, 0, u 2, u 3, 0, u 4, u 5, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, u 0, -u 0, -u 0, u 1, 0, 0, u 2, u 3, u 3, -u 3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, u 0, -u 0, u 1, u 2, 0, 0, u 3, u 4, u 5, -u 5, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, u 0, u 1, u 2, u 3, 0, 0, u 4, u 5, u 6, u 7, 0, 0, 0, 0, 0], ![u 0, -u 0, -u 0, -u 0, -u 0, -u 0, u 0, -u 0, -u 0, u 0, -u 0, u 0, u 0, -u 0, u 0, u 0, u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, -u 0, -u 0, -u 0, u 0, -u 0, -u 0, u 0, u 0, -u 0, -u 0, u 0, -u 0, -u 0, -u 0, -u 0, -u 0, u 0], ![u 0, -u 0, -u 0, -u 0, -u 0, -u 0, u 0, u 0, -u 0, u 0, -u 0, u 0, -u 0, -u 0, u 0, u 0, u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, -u 0, -u 0, -u 0, u 0, u 1, -u 0, u 0, -u 0, u 0, u 2, -u 0, u 0, u 0, u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, -u 0, -u 0, u 0, u 0, -u 0, u 0, u 0, u 0, u 0, -u 0, u 0, u 0, -u 0, -u 0, -u 0, -u 0, u 0], ![u 0, -u 0, -u 0, -u 0, -u 0, u 0, u 0, u 1, -u 1, u 0, u 0, u 2, -u 2, u 0, u 0, -u 0, -u 0, -u 0, -u 0, u 0], ![u 0, -u 0, -u 0, u 0, -u 0, u 0, -u 0, u 0, u 0, -u 0, u 0, -u 0, -u 0, u 0, -u 0, u 0, -u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, u 0, -u 0, u 0, -u 0, u 0, u 0, u 1, u 2, -u 0, -u 0, u 0, -u 0, u 0, -u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, u 0, -u 0, u 0, -u 0, u 1, -u 1, -u 0, u 0, u 2, -u 2, u 0, -u 0, u 0, -u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, u 0, -u 0, u 0, -u 0, u 1, u 2, -u 0, u 0, u 3, u 4, u 0, -u 0, u 0, -u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, u 0, -u 0, u 1, -u 0, u 0, u 1, -u 1, u 1, -u 1, -u 0, u 0, -u 1, u 0, -u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, u 0, u 1, -u 1, -u 0, u 0, -u 1, u 2, -u 1, u 2, -u 0, u 0, u 2, -u 2, -u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, u 0, u 1, -u 1, -u 0, u 0, -u 1, u 2, u 3, u 1, -u 0, u 0, u 1, -u 1, -u 0, u 0, u 0, -u 0]]

def complementCoord : Fin 20 → Fin 20 :=
  ![19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem complementCoord_masks (i : Fin 20) :
    tripleMasks (complementCoord i) = Nat.xor (tripleMasks i) 63 := by
  revert i
  decide +kernel

/-- The coefficient-support conclusion of A.4, in the exact twenty-triple encoding. -/
def OneComplementPair {K : Type*} [Zero K] (q : Fin 20 → K) : Prop :=
  ∃ i : Fin 20, ∀ j, q j ≠ 0 → j = i ∨ j = complementCoord i

end Paper2.Certificates.Q6
