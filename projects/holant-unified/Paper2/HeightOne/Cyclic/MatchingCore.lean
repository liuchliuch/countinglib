import Paper2.HeightOne.Cyclic.PerfectWeightTwo
import Paper2.HeightOne.Cyclic.PairingFromInvolution
import Paper2.HeightOne.Cyclic.NonemptyWeightTwo
import Paper2.HeightOne.Cyclic.Source

/-! The full supported weight-two matching of a minimum cyclic core. The
support constraint is proved before introducing any coefficient factorization. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable ExactInput GroupSplit GroupSplit.MatrixGroup PhaseCards EndpointSelfLoop

/-- The supported weight-two graph itself supplies a perfect pairing of all
original ports, and every supported word obeys it. -/
theorem matching_core_of_cards {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : f ≠ 0) (hn : 6 ≤ n) (S : Set AlgebraicComplex)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ u ∈ S, s ≠ t ∧ s ≠ u ∧ t ≠ u)
    (hcards : ∀ a b (hab : a ≠ b), ∀ q ∈ S, plusContraction a b hab q f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab q f))
    (hprod : ∀ a b (hab : a ≠ b), ∀ q ∈ S,
      Product (Tensor.reindex (Fintype.equivFin (Remaining a b)) (plusContraction a b hab q f))) :
    ∃ P : Pairing n,
      (∀ i, f (pairWord (P.ports (i, false)) (P.ports (i, true))) ≠ 0) ∧
      support f ⊆ equalityCode P := by
  have hedge : ∃ u v, WeightTwoRel f u v := exists_weightTwo_of_matching_product_cards f hf hn S hthree hcards hprod
  have htotal := weightTwo_is_perfect f hf hn S hthree hcards hedge
  have hs : Symmetric (WeightTwoRel f) := by
    intro u v huv
    exact ⟨Ne.symm huv.1, by rw [pairWord_comm]; exact huv.2⟩
  obtain ⟨P, hP⟩ := pairing_of_unique_neighbours (WeightTwoRel f) hs
    (fun u hu => hu.1 rfl)
    (fun u v w hv hw => weightTwo_unique_partner f hf (by omega) S hthree hcards
      u v w hv.1 hw.1 hv.2 hw.2) htotal
  refine ⟨P, fun i => (hP i).2, ?_⟩
  intro x hx
  rw [mem_support] at hx
  rw [mem_equalityCode]
  intro i
  exact weightTwo_forces_equality f hf (by omega) S hthree hcards
    _ _ (hP i).1 (hP i).2 x hx

variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]

/-- Actual normalized minimum-prime source theorem: its original Walsh
support has one perfect matching, and every matching edge is supported. -/
theorem minimum_walsh_matching_core (C : RotationCards F N) (L : Language)
    (hN : 3 ≤ N) (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hn : 6 ≤ n) (hG : actualClasses L.family = cyclicPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n) (hf : f ≠ 0)
    (hprocessed : (rotationMenu C).Processed ⟨n, f⟩ L) :
    ∃ P : Pairing n,
      (∀ i, walshCoordinates f (pairWord (P.ports (i, false)) (P.ports (i, true))) ≠ 0) ∧
      support (walshCoordinates f) ⊆ equalityCode P := by
  apply matching_core_of_cards (walshCoordinates f) (walsh_nonzero f hf) hn {s | s ^ N = 1}
    (three_algebraic_root_phases N hN)
    (minimum_root_matching_cards C L heven hsafe hG hmin f hprocessed)
  intro a b hab s hs
  let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
  exact minimum_plusCard_product C L heven hsafe (Or.inl hG) hmin f hprocessed a b hab r

end
end Paper2.HeightOne.Cyclic
