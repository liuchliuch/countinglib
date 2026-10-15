import Paper2.HeightOne.Dihedral.SixPortAllCards
import Paper2.HeightOne.Dihedral.ActualMatching
import Paper2.HeightOne.TensorPrimeTools

/-! The actual six-port dihedral minimum-prime endpoint. Every analytic card
is supplied by the finite real representative menu and its retained selected
binary factors; all parity, support, and coefficient conclusions are discharged
by the preceding signed-pencil proof. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Cyclic Tractable ExactInput EndpointSelfLoop PhaseCards GroupSplit GroupSplit.MatrixGroup

lemma MatchingCosetSupport.toAffine {ι : Type} [Fintype ι]
    {f : Tensor AlgebraicComplex ι} (h : MatchingCosetSupport f) : CosetMatchingSupport f := by
  obtain ⟨P,d,h⟩ := h
  exact ⟨P,Matching.word P d (fun _ => false),h.trans (cosetCode_matchingWords P d).symm⟩

variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]

/-- A fully processed actual six-port core has a genuine ordered decomposition
into three binary tensors. No matching support, coefficient determinant, parity
or abstract card-rigidity premise is supplied by the caller. -/
theorem minimum_six_binary_decomposition (C : XorCards F N) (L : Language)
    (hN : 3 ≤ N) (heven : ∀ f ∈ L.family, Even f.1)
    (hsafe : AllBinariesSafe L.family)
    (hG : actualClasses L.family = dihedralPhaseClasses N)
    (hmin : LeastPrimeArity L.family 6) (f : Signature AlgebraicComplex 6) (hf : f ≠ 0)
    (hprocessed : (xorMenu C).Processed ⟨6,f⟩ L) :
    ∃ D : TensorDecomposition AlgebraicComplex 6, D.value = f ∧ ∀ i, D.arity i = 2 := by
  classical
  have hw := walsh_nonzero f hf
  obtain ⟨a,ha⟩ : ∃ a,walshCoordinates f a ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  obtain ⟨s,hs,t,ht,u,hu,hst,hsu,htu⟩ := three_algebraic_root_phases N hN
  have H (q : AlgebraicComplex) (hq : q ^ N = 1) : q ≠ 0 := by
    intro hz
    simp [hz,NeZero.ne N] at hq
  have hqroot : ∀ q : AlgebraicComplex,q = s ∨ q = t ∨ q = u → q ^ N = 1 := by
    intro q hq
    rcases hq with rfl | rfl | rfl <;> assumption
  obtain ⟨D,hD,htwo⟩ := six_binary_decomposition_of_all_xor_cards (walshCoordinates f)
    a ha s t u hst hsu htu (H s hs) (H t ht) (H u hu)
    (fun i j hij v w q hq hn => by
      let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq q (hqroot q hq)
      have hh := minimum_xorCard_coset C L heven hsafe hG hmin f hprocessed
        i j hij v w r (by simpa only [r,rootsOfUnity.coe_mkOfPowEq] using hn)
      exact hh.toAffine)
    (fun i j hij v w q hq => by
      let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq q (hqroot q hq)
      simpa only [r,rootsOfUnity.coe_mkOfPowEq] using
        minimum_xorCard_product C L heven hsafe hG hmin f hprocessed i j hij v w r)
  refine ⟨D.mapAction walsh,?_,htwo⟩
  rw [TensorDecomposition.value_mapAction,hD]
  change walshBasis.action (walshCoordinates f) = f
  rw [← walshBasis_inverse_action,InvertibleKernel.action_symm_action]

/-- The source six-port base excludes an actual minimum tensor-prime core. -/
theorem minimum_six_not_tensorPrime (C : XorCards F N) (L : Language)
    (hN : 3 ≤ N) (heven : ∀ f ∈ L.family, Even f.1)
    (hsafe : AllBinariesSafe L.family)
    (hG : actualClasses L.family = dihedralPhaseClasses N)
    (hmin : LeastPrimeArity L.family 6) (f : Signature AlgebraicComplex 6)
    (hprocessed : (xorMenu C).Processed ⟨6,f⟩ L) : ¬ TensorPrime f := by
  intro hp
  obtain ⟨D,hD,htwo⟩ := minimum_six_binary_decomposition C L hN heven hsafe hG hmin f hp.1 hprocessed
  apply binary_decomposition_not_tensorPrime D htwo (by decide)
  rwa [hD]

end
end Paper2.HeightOne.Dihedral

