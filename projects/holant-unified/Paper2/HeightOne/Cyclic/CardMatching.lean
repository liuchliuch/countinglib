import Paper2.HeightOne.Cyclic.MatchingSupport
import Paper2.HeightOne.MinimumPrime
import Paper2.HeightOne.PhaseCards.WalshProduct

/-! At a least nonbinary prime, the selected actual card decomposition gives
literal equality-matching Walsh support. No parity or matching of the original
tensor is assumed, and every coefficient of every binary factor is retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable ExactInput GroupSplit GroupSplit.MatrixGroup PhaseCards
open scoped BigOperators

/-- An ordered pairing induced by a decomposition all of whose factors have
exactly two ports; the original factor and external port orders are retained. -/
def decompositionPairing {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (htwo : ∀ i, D.arity i = 2) : Pairing n where
  count := D.count
  ports := (((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans
    (Equiv.sigmaEquivProd (Fin D.count) (Fin 2)).symm).trans
    (Equiv.sigmaCongrRight (fun i => finCongr (htwo i))).symm).trans D.ports

lemma decomposition_equality_support {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (htwo : ∀ i, D.arity i = 2)
    (hfactor : ∀ i x, D.factor i x ≠ 0 ↔
      x (Fin.cast (htwo i).symm 0) = x (Fin.cast (htwo i).symm 1)) :
    support D.value = equalityCode (decompositionPairing D htwo) := by
  classical
  ext x
  rw [mem_support, mem_equalityCode]
  simp only [TensorDecomposition.value, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]
  simp only [hfactor]
  exact and_iff_right (Units.ne_zero D.scale)

lemma cyclic_binary_diagonal_support {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N) {B : AMat} (hB : ActualNonsingular F B) :
    ∀ x, walshCoordinates (binarySignature B) x ≠ 0 ↔ x 0 = x 1 := by
  obtain ⟨U, hU, hu⟩ := actual_transfer_GL hB
  rw [hG] at hu
  obtain ⟨s, hs, he⟩ := hu
  have he' := pglMk_eq_iff_projectiveClass_eq.mp he.symm
  rw [hU] at he'
  obtain ⟨c, hc, hm⟩ := projectiveClass_eq_iff.mp he'
  have hs0 : (s : AlgebraicComplex) ≠ 0 := Units.ne_zero s
  intro x
  rw [walshCoordinates_binary, rotation_walsh_binary hm]
  cases hx0 : x 0 <;> cases hx1 : x 1 <;>
    simp [binarySignature, PhaseCards.plusKernel, hx0, hx1, hc, hs0]

lemma cyclic_signature_diagonal_support {F : SignatureFamily AlgebraicComplex} {N n : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N) (hsafe : AllBinariesSafe F)
    (f : Signature AlgebraicComplex n) (hn : n = 2)
    (hr : NetworkRealizable F f) (hp : f ≠ 0) :
    ∀ x, walshCoordinates f x ≠ 0 ↔ x (Fin.cast hn.symm 0) = x (Fin.cast hn.symm 1) := by
  subst n
  have h := cyclic_binary_diagonal_support hG (actual_tableBinary hsafe f hr hp)
  simpa only [binarySignature_tableBinary, Fin.cast_refl, id_eq] using h

/-- A literal tensor decomposition into retained nonsingular cyclic binaries
has a real perfect-matching support in the fixed Walsh coordinates. -/
theorem decomposition_walsh_matching {F : SignatureFamily AlgebraicComplex} {N n : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N) (hsafe : AllBinariesSafe F)
    (D : TensorDecomposition AlgebraicComplex n)
    (hmem : ∀ i, (⟨D.arity i, D.factor i⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hprime : ∀ i, TensorPrime (D.factor i)) (htwo : ∀ i, D.arity i = 2) :
    ∃ P : Pairing n, support (walshCoordinates D.value) = equalityCode P := by
  let Q := D.mapAction walshInv
  have hQ : ∀ i, Q.arity i = 2 := htwo
  have hdiag : ∀ i x, Q.factor i x ≠ 0 ↔
      x (Fin.cast (hQ i).symm 0) = x (Fin.cast (hQ i).symm 1) := by
    intro i
    have h := cyclic_signature_diagonal_support hG hsafe (D.factor i) (htwo i)
      (networkRealizable_of_mem (hmem i)) (hprime i).1
    simpa only [Q, TensorDecomposition.mapAction, ← walshCoordinates_eq_coordinateAction] using h
  have hvalue : Q.value = walshCoordinates D.value :=
    (TensorDecomposition.value_mapAction D walshInv).trans (walshCoordinates_eq_coordinateAction D.value).symm
  exact ⟨decompositionPairing Q hQ, hvalue ▸ decomposition_equality_support Q hQ hdiag⟩

/-- Minimality plus full actual saturation supplies the matching premise for
every nonzero positive-arity chosen card, rather than assuming that premise. -/
theorem minimum_card_walsh_matching {F : SignatureFamily AlgebraicComplex}
    (M : BinaryMenu F) (L : Language) (heven : ∀ f ∈ L.family, Even f.1)
    (hsafe : AllBinariesSafe L.family) {N n : ℕ}
    (hG : actualClasses L.family = cyclicPhaseClasses N) (hmin : LeastPrimeArity L.family n)
    (f : AnySignature AlgebraicComplex) (hf : f.1 = n) (hprocessed : M.Processed f L)
    (k : M.Choices f) (hcard : 0 < (M.produced f k).1 ∧ (M.produced f k).2 ≠ 0) :
    ∃ P : Pairing (M.produced f k).1,
      support (walshCoordinates (M.produced f k).2) = equalityCode P := by
  let Q := selectedDecomposition (M.produced f k) hcard
  have hQ := selectedDecomposition_spec (M.produced f k) hcard
  have hc (i : Fin Q.count) : (⟨Q.arity i, Q.factor i⟩ : AnySignature AlgebraicComplex) ∈ M.children f := by
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [selectedFactors, dif_pos hcard]
    exact ⟨i, rfl⟩
  have hmem := fun i => hprocessed.2.1 (hc i)
  have htwo : ∀ i, Q.arity i = 2 := fun i =>
    selected_card_factors_binary M L heven hmin f hf hprocessed (hc i)
  obtain ⟨P, hP⟩ := decomposition_walsh_matching hG hsafe Q hmem hQ.2.2 htwo
  rw [hQ.1] at hP
  exact ⟨P, hP⟩

end
end Paper2.HeightOne.Cyclic
