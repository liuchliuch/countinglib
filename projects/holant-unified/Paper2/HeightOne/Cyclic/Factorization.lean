import Paper2.HeightOne.Cyclic.DiagonalIntegration
import Paper2.HeightOne.Cyclic.ThreeBlockIntegration

/-! Reconstruct the complete original tensor from its proved logical product,
retaining all binary factors, named ports and the exact nonzero scalar. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable ExactInput GroupSplit GroupSplit.MatrixGroup PhaseCards EndpointSelfLoop
open scoped BigOperators

def equalityBinary (r : AlgebraicComplex) : Signature AlgebraicComplex 2 :=
  fun x => if x 0 = x 1 then (if x 0 then r else 1) else 0

def equalityDecomposition {n : ℕ} (P : Pairing n) (c : AlgebraicComplex) (hc : c ≠ 0)
    (ρ : Fin P.count → AlgebraicComplex) : TensorDecomposition AlgebraicComplex n where
  count := P.count
  arity _ := 2
  factor i := equalityBinary (ρ i)
  ports := ((Equiv.sigmaEquivProd (Fin P.count) (Fin 2)).trans
    (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)).trans P.ports
  scale := Units.mk0 c hc

lemma equalityDecomposition_value {n : ℕ} (P : Pairing n) (c : AlgebraicComplex) (hc : c ≠ 0)
    (ρ : Fin P.count → AlgebraicComplex) (x : Fin n → Bool) :
    (equalityDecomposition P c hc ρ).value x = c * ∏ i,
      if x (P.ports (i, false)) = x (P.ports (i, true)) then
        (if x (P.ports (i, false)) then ρ i else 1) else 0 := rfl

/-- Logical unary coefficients give an actual finite ordered decomposition of
f, including its vanishing coefficients outside the matching code. -/
theorem decomposition_of_logical_product {n : ℕ} (f : Signature AlgebraicComplex n) (P : Pairing n)
    (hF : support f ⊆ equalityCode P) (h0 : f (fun _ => false) ≠ 0)
    (ρ : Fin P.count → AlgebraicComplex)
    (hρ : ∀ t, f (blockWord P t) = f (fun _ => false) * ∏ i, (if t i then ρ i else 1)) :
    (equalityDecomposition P (f (fun _ => false)) h0 ρ).value = f := by
  classical
  funext x
  rw [equalityDecomposition_value]
  by_cases hx : x ∈ equalityCode P
  · have he := (mem_equalityCode P x).mp hx
    simp only [he, ↓reduceIte]
    have h := hρ (fun i => x (P.ports (i, false)))
    rw [reconstruct_blockWord P x hx] at h
    simpa only [he] using h.symm
  · have hfx : f x = 0 := by
      by_contra h
      exact hx (hF ((mem_support _ _).mpr h))
    rw [hfx]
    apply mul_eq_zero_of_right
    rw [mem_equalityCode] at hx
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]

/-- A minimum cyclic core at any arity at least six genuinely factors into
ordered binaries. The six-port case uses three-phase minors; larger arities
use only official Paper 1 Lemma 7.8 with its hypotheses proved above. -/
theorem minimum_higher_binary_decomposition (P1 : Paper1DiagonalSlicesAccepted)
    (C : RotationCards F N) (L : Language) (hN : 3 ≤ N)
    (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hn : 6 ≤ n) (hG : actualClasses L.family = cyclicPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n) (hf : f ≠ 0)
    (hprocessed : (rotationMenu C).Processed ⟨n, f⟩ L) :
    ∃ D : TensorDecomposition AlgebraicComplex n, D.value = f ∧ ∀ i, D.arity i = 2 := by
  obtain ⟨P, hedges, hP⟩ := minimum_walsh_matching_core C L hN heven hsafe hn hG hmin f hf hprocessed
  have hc : 3 ≤ P.count := by have h := Matching.pair_count P; omega
  have h0 := minimum_walsh_origin_nonzero C L hN heven hsafe (by omega) hG hmin f hf hprocessed
  have hm := minimum_root_matching_cards C L heven hsafe hG hmin f hprocessed
  have hp : ∀ a b (hab : a ≠ b), ∀ s : AlgebraicComplex, s ^ N = 1 →
      Product (Tensor.reindex (Fintype.equivFin (Remaining a b))
        (plusContraction a b hab s (walshCoordinates f))) := by
    intro a b hab s hs
    let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
    exact minimum_plusCard_product C L heven hsafe (Or.inl hG) hmin f hprocessed a b hab r
  have hfactor : ∃ ρ : Fin P.count → AlgebraicComplex, (∀ i, ρ i ≠ 0) ∧
      ∀ t, walshCoordinates f (blockWord P t) = walshCoordinates f (fun _ => false) *
        ∏ i, (if t i then ρ i else 1) := by
    by_cases hthree : P.count = 3
    · obtain ⟨s, hs, t, ht, u, hu, hst, hsu, htu⟩ := three_algebraic_root_phases N hN
      apply logical_three_factorization (walshCoordinates f) P hthree hP h0 s t u hst hsu htu
      · intro a b hab q hq
        exact hm a b hab q (hq.elim (fun he => he ▸ hs) (fun hq => hq.elim (fun he => he ▸ ht) (fun he => he ▸ hu)))
      · intro a b hab q hq
        exact hp a b hab q (hq.elim (fun he => he ▸ hs) (fun hq => hq.elim (fun he => he ▸ ht) (fun he => he ▸ hu)))
    · exact logical_large_factorization P1 (walshCoordinates f) P (by omega) hP h0 1 one_ne_zero
        (fun a b hab => hm a b hab 1 (one_pow N)) (fun a b hab => hp a b hab 1 (one_pow N))
  obtain ⟨ρ, hρ, hform⟩ := hfactor
  let Q := equalityDecomposition P (walshCoordinates f (fun _ => false)) h0 ρ
  have hQ : Q.value = walshCoordinates f := decomposition_of_logical_product (walshCoordinates f) P hP h0 ρ hform
  refine ⟨Q.mapAction walsh, ?_, fun _ => rfl⟩
  rw [TensorDecomposition.value_mapAction, hQ]
  change walshBasis.action (walshCoordinates f) = f
  rw [← walshBasis_inverse_action, InvertibleKernel.action_symm_action]

end
end Paper2.HeightOne.Cyclic
