import Paper2.SourceFaithful.SourceStatements.TypeParityStatement
import Paper2.HeightOne.Cyclic.ActualDeck

/-! Literal ordered prime factors of a source contraction determine its full
Walsh matching support and Product coefficients. No saturation, preprocessing,
or parity assumption on an ambient language is used. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Paper2.SourceFaithful.SourceStatements.CyclicCardFactorBridge
noncomputable section
open Tractable HeightOne HeightOne.PhaseCards HeightOne.Cyclic
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup
open HeightOne.GroupSplit.FiniteGroupFacts.ProjectiveCentralizers
open EndpointSelfLoop TypeParityStatement

/-- Every positive factor in every actual ordered prime decomposition is a
binary whose literal Walsh transfer lies in the displayed cyclic group. The
nonzero scale and root of unity in this membership force nonsingularity. -/
def PrimeFactorsCyclicBinary {ι : Type} [Fintype ι] (N : ℕ)
    (f : Tensor AlgebraicComplex ι) : Prop :=
  ∀ (m : ℕ) (D : TensorDecomposition AlgebraicComplex m) (e : Fin m ≃ ι),
    Tensor.reindex e D.value = f →
    (∀ i, 0 < D.arity i) → (∀ i, TensorPrime (D.factor i)) →
    ∀ i, ∃ h : D.arity i = 2,
      WalshTransferMember .cyclic N (tableBinary (h ▸ D.factor i))

lemma cyclic_binary_data {N : ℕ} (f : Signature AlgebraicComplex 2)
    (h : WalshTransferMember .cyclic N (tableBinary f)) :
    (∀ x, walshCoordinates f x ≠ 0 ↔ x 0 = x 1) ∧
      Product (walshCoordinates f) := by
  rcases h with ⟨s, c, hc, ht⟩ | ⟨hk, _⟩
  · have hs : (s.val : AlgebraicComplex) ≠ 0 := Units.ne_zero s.val
    have h00 : walshBinary (tableBinary f) false false = c := by
      have he := congrArg (fun M : AMat => M false false) ht
      simpa [Matrix.mul_apply, zGL, diagonalGL, diagonal] using he
    have h01 : walshBinary (tableBinary f) false true = 0 := by
      have he := congrArg (fun M : AMat => M false true) ht
      simpa [Matrix.mul_apply, zGL, diagonalGL, diagonal] using he
    have h10 : walshBinary (tableBinary f) true false = 0 := by
      have he := congrArg (fun M : AMat => M true false) ht
      simpa [Matrix.mul_apply, zGL, diagonalGL, diagonal] using he
    have h11 : walshBinary (tableBinary f) true true = -(c * (s.val : AlgebraicComplex)) := by
      have he := congrArg (fun M : AMat => M true true) ht
      have he' : -walshBinary (tableBinary f) true true = c * (s.val : AlgebraicComplex) := by
        simpa [Matrix.mul_apply, zGL, diagonalGL, diagonal] using he
      exact neg_eq_iff_eq_neg.mp he'
    have hw : walshCoordinates f = binarySignature (walshBinary (tableBinary f)) := by
      simpa only [binarySignature_tableBinary] using walshCoordinates_binary (tableBinary f)
    constructor
    · intro x
      rw [hw]
      cases h0 : x 0 <;> cases h1 : x 1 <;>
        simp [binarySignature, h0, h1, h00, h01, h10, h11, hc, hs]
    · rw [hw]
      exact diagonal_binary_product _ h01 h10
  · cases hk

lemma cyclic_factor_data {N m : ℕ} (f : Signature AlgebraicComplex m)
    (h2 : m = 2) (h : WalshTransferMember .cyclic N (tableBinary (h2 ▸ f))) :
    (∀ x, walshCoordinates f x ≠ 0 ↔
      x (Fin.cast h2.symm 0) = x (Fin.cast h2.symm 1)) ∧
      Product (walshCoordinates f) := by
  subst m
  simpa using cyclic_binary_data f h

/-- Exact support and coefficient normal form of the original contraction,
after the fixed analytic Walsh coordinate change. -/
theorem matching_product_of_prime_factors {ι : Type} [Fintype ι] {N : ℕ}
    (f : Tensor AlgebraicComplex ι) (hn : 0 < Fintype.card ι) (hf : f ≠ 0)
    (h : PrimeFactorsCyclicBinary N f) :
    EqualityMatchingSupport (walshCoordinates f) ∧
      Product (Tensor.reindex (Fintype.equivFin ι) (walshCoordinates f)) := by
  classical
  obtain ⟨D, hval, hpos, hprime⟩ := prime_decomposition_ports f hn hf
  have hd := h _ D (Fintype.equivFin ι).symm hval hpos hprime
  choose htwo hmember using hd
  let Q := D.mapAction walshInv
  have hQtwo : ∀ i, Q.arity i = 2 := htwo
  have hdata (i : Fin D.count) := cyclic_factor_data (D.factor i) (htwo i) (hmember i)
  have hdiag : ∀ i x, Q.factor i x ≠ 0 ↔
      x (Fin.cast (hQtwo i).symm 0) = x (Fin.cast (hQtwo i).symm 1) := by
    intro i
    simpa only [Q, TensorDecomposition.mapAction,
      ← walshCoordinates_eq_coordinateAction] using (hdata i).1
  have hprod : Product Q.value := Product.decomposition Q (fun i => by
    simpa only [Q, TensorDecomposition.mapAction,
      ← walshCoordinates_eq_coordinateAction] using (hdata i).2)
  have hv : Q.value = Tensor.reindex (Fintype.equivFin ι) (walshCoordinates f) := by
    have he := decomposition_walsh D (Fintype.equivFin ι).symm
    rw [hval] at he
    funext x
    have he' := congrFun he (fun i => x ((Fintype.equivFin ι) i))
    change Q.value (fun i => x ((Fintype.equivFin ι)
      ((Fintype.equivFin ι).symm i))) = _ at he'
    change Q.value x = walshCoordinates f (fun i => x ((Fintype.equivFin ι) i))
    simpa only [Equiv.apply_symm_apply] using he'
  constructor
  · refine ⟨decompositionPairing Q hQtwo, ?_⟩
    rw [← hv]
    exact decomposition_equality_support Q hQtwo hdiag
  · exact hv ▸ hprod

/-- The source's card-factor condition, for every literal ordered port pair,
chosen representative, and orientation. Zero contractions remain allowed. -/
def CyclicCardFactors {N n : ℕ} (R : Representatives .cyclic N)
    (f : Signature AlgebraicComplex n) : Prop :=
  ∀ (a b : Fin n) (hab : a ≠ b) (r : RepresentativeIndex .cyclic N)
    (orientation : Bool), contraction R a b hab r orientation f ≠ 0 →
      PrimeFactorsCyclicBinary N (contraction R a b hab r orientation f)

/-- Original cards supply the analytic matching and Product hypotheses. The
identity includes the actual nonzero `2 * scale` and surviving port order. -/
theorem root_card_data {N n : ℕ} [NeZero N] (R : Representatives .cyclic N)
    (f : Signature AlgebraicComplex n) (hn : 3 ≤ n) (hcards : CyclicCardFactors R f)
    (a b : Fin n) (hab : a ≠ b) (s : AlgebraicComplex) (hs : s ^ N = 1) :
    (plusContraction a b hab s (walshCoordinates f) ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab s (walshCoordinates f))) ∧
    Product (Tensor.reindex (Fintype.equivFin (Remaining a b))
      (plusContraction a b hab s (walshCoordinates f))) := by
  classical
  let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
  let g := contraction R a b hab (rotationIndex .cyclic r) false f
  let c := 2 * R.scale (rotationIndex .cyclic r)
  have hc : c ≠ 0 := mul_ne_zero (by norm_num) (R.scale_ne_zero _)
  have ht : transfer (R.binary (rotationIndex .cyclic r)) =
      R.scale (rotationIndex .cyclic r) • phase r.val := by
    simpa only [rotationIndex, Bool.false_eq_true, ite_false] using
      R.transfer_eq (rotationIndex .cyclic r)
  have hw : walshCoordinates g = c • plusContraction a b hab s (walshCoordinates f) := by
    simpa only [g, c, contraction, orientedBinary, Bool.false_eq_true, ite_false,
      r, rootsOfUnity.coe_mkOfPowEq] using rotation_card_walsh a b hab f ht
  by_cases hz : plusContraction a b hab s (walshCoordinates f) = 0
  · constructor
    · exact fun h => False.elim (h hz)
    · rw [hz]
      convert product_zero (Fintype.card (Remaining a b)) using 1
      rfl
  · have hg : g ≠ 0 := by
      intro hg
      rw [hg, walsh_zero] at hw
      apply hz
      funext x
      have he := congrFun hw x
      exact (mul_eq_zero.mp (by simpa only [Pi.zero_apply, Pi.smul_apply,
        smul_eq_mul] using he.symm)).resolve_left hc
    have hp : 0 < Fintype.card (Remaining a b) := by
      have he := remaining_card a b hab
      simp only [Fintype.card_fin] at he
      omega
    obtain ⟨hm, hprod⟩ := matching_product_of_prime_factors g hp hg
      (hcards a b hab _ false hg)
    have he : Tensor.reindex (Fintype.equivFin (Remaining a b)) (walshCoordinates g) =
        c • Tensor.reindex (Fintype.equivFin (Remaining a b))
          (plusContraction a b hab s (walshCoordinates f)) := by
      rw [hw]
      rfl
    constructor
    · intro _
      obtain ⟨P, hP⟩ := hm
      refine ⟨P, ?_⟩
      rw [he, support_smul c hc] at hP
      exact hP
    · have hscaled := hprod.scale c⁻¹
      rw [he] at hscaled
      simpa only [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hc, one_mul] using hscaled

end
end Paper2.SourceFaithful.SourceStatements.CyclicCardFactorBridge

