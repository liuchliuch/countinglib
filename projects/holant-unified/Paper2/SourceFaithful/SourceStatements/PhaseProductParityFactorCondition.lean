import Paper2.SourceFaithful.SourceStatements.PhaseProductParityStatement
import Paper2.SourceFaithful.SourceStatements.PhaseProductParityTransfer
import Paper2.SourceFaithful.SourceStatements.PhaseProductParityPrimeDecomposition
import Paper2.SourceFaithful.SourceStatements.PhaseProductPrimeAssembly

/-! The literal positive-prime-factor condition (C) at residual arity two.
Its equivalence with the whole-binary test uses actual prime decomposition
existence and a proved singleton decomposition, including the recorded scale
and ordered ports. It is not supplied as a classification certificate. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup
open TypeParityStatement PhaseProductDecomposition
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Every positive tensor-prime factor in every actual ordered decomposition
is a binary with its literal Walsh transfer in the displayed dihedral group.
The nonzero group scale forces nonsingularity. Nullary factors have already
been absorbed in the unit scale of the positive decomposition. -/
def PrimeFactorsDihedralBinary {ι : Type} [Fintype ι] (N : ℕ)
    (f : Tensor AlgebraicComplex ι) : Prop :=
  ∀ (m : ℕ) (D : TensorDecomposition AlgebraicComplex m) (e : Fin m ≃ ι),
    Tensor.reindex e D.value = f →
    (∀ i, 0 < D.arity i) → (∀ i, TensorPrime (D.factor i)) →
    ∀ i, ∃ h : D.arity i = 2,
      (tableBinary (h ▸ D.factor i)).det ≠ 0 ∧
      WalshTransferMember .dihedral N (tableBinary (h ▸ D.factor i))

lemma phaseProduct_of_binary_phase {N : ℕ} (hN : 0 < N)
    (f : Signature AlgebraicComplex 2) (hf : BinaryPhase N f) : PhaseProduct N f := by
  rcases (binary_phase_iff_pair hN (by simp) f).mp hf with hz | ⟨a,c,s,_,hs,he⟩
  · rw [hz]
    exact PhaseProduct.zero N _
  · rw [he]
    exact (PhaseProduct.of_block
      ⟨0,a,-s,rfl,phaseRatio_one_negative hN hs,rfl⟩).scale c

lemma phaseProduct_of_transfer {N : ℕ} (hN : 0 < N)
    (f : Signature AlgebraicComplex 2)
    (hf : WalshTransferMember .dihedral N (tableBinary f)) :
    PhaseProduct N (walshCoordinates f) :=
  phaseProduct_of_binary_phase hN _ ((walshTransfer_dihedral_iff hN f).mp hf).2

lemma phaseProduct_of_transfer_cast {N m : ℕ} (hN : 0 < N)
    (f : Signature AlgebraicComplex m) (h2 : m = 2)
    (hf : WalshTransferMember .dihedral N (tableBinary (h2 ▸ f))) :
    PhaseProduct N (walshCoordinates f) := by
  subst m
  exact phaseProduct_of_transfer hN f hf

theorem binary_phase_of_prime_factors {N : ℕ} (hN : 0 < N)
    {ι : Type} [Fintype ι] (hc : Fintype.card ι = 2)
    (f : Tensor AlgebraicComplex ι) (h : PrimeFactorsDihedralBinary N f) :
    BinaryPhase N (walshCoordinates f) := by
  apply binary_phaseProduct hN hc _
  apply phaseProduct_of_prime_factors f
  intro m D e he hpos hprime i
  obtain ⟨h2,_,hm⟩ := h m D e he hpos hprime i
  exact phaseProduct_of_transfer_cast hN (D.factor i) h2 hm

lemma tensorPrime_of_binary_phase {N : ℕ} (hN : 0 < N)
    (f : Signature AlgebraicComplex 2) (hf : f ≠ 0)
    (h : BinaryPhase N (walshCoordinates f)) : TensorPrime f := by
  have hw : TensorPrime (walshCoordinates f) := by
    rcases (binary_phase_iff_pair hN (by simp) (walshCoordinates f)).mp h with
      hz | ⟨a,c,s,hc,hs,he⟩
    · exact False.elim (walshCoordinates_ne_zero hf hz)
    · rw [he]
      exact tensorPrime_twoPoint (by decide) a c (-s) hc
        (neg_ne_zero.mpr (root_ne_zero hN hs))
  have hi := tensorPrime_action_iff walshBasis.symm f
  rw [walshBasis_inverse_action] at hi
  exact hi.mp hw

/-- A nonzero binary passing the whole-table phase test has exactly one
positive prime factor in every actual decomposition. Its group membership
survives the exact decomposition scale and either port permutation. -/
theorem prime_factors_of_binary_phase {N : ℕ} (hN : 0 < N)
    {ι : Type} [Fintype ι] (hc : Fintype.card ι = 2)
    (f : Tensor AlgebraicComplex ι) (hf : f ≠ 0)
    (h : BinaryPhase N (walshCoordinates f)) : PrimeFactorsDihedralBinary N f := by
  classical
  intro m D e he hpos hprime
  have hm : m = 2 := by simpa using (Fintype.card_congr e).trans hc
  subst m
  have hD : BinaryPhase N (walshCoordinates D.value) := by
    have hh := h.reindex e.symm
    rw [← he,walshCoordinates_reindex,Tensor.reindex_trans] at hh
    simpa using hh
  have hz : D.value ≠ 0 := by
    intro hz
    apply hf
    rw [← he,hz]
    rfl
  have hp := tensorPrime_of_binary_phase hN D.value hz hD
  have hcount := prime_count_one D (by decide) hp hpos
  rcases D with ⟨count,arity,factor,ports,scale⟩
  change count = 1 at hcount
  subst count
  have hs : ∑ i, arity i = 2 := by simpa using Fintype.card_congr ports
  have har : arity = fun _ => 2 := by
    funext i
    have hi := Fin.eq_zero i
    subst i
    simpa using hs
  subst arity
  let ep : Fin 2 ≃ Fin 2 :=
    (Equiv.uniqueSigma (fun _ : Fin 1 => Fin 2)).symm.trans ports
  have hv : (TensorDecomposition.mk 1 (fun _ => 2) factor ports scale).value =
      (scale : AlgebraicComplex) • Tensor.reindex ep (factor 0) := by
    funext x
    simp [TensorDecomposition.value,Tensor.reindex,ep]
  rw [hv] at hD
  change BinaryPhase N (walshCoordinates
    (fun x => (scale : AlgebraicComplex) * Tensor.reindex ep (factor 0) x)) at hD
  rw [walshCoordinates_scale,walshCoordinates_reindex] at hD
  have hF := (BinaryPhase.scale_iff _ _ (Units.ne_zero scale)).mp hD
  have hF' := hF.reindex ep.symm
  rw [Tensor.reindex_trans] at hF'
  have hzero : BinaryPhase N (walshCoordinates (factor 0)) := by simpa using hF'
  intro i
  have hi := Fin.eq_zero i
  subst i
  have hm := (walshTransfer_dihedral_iff hN (factor 0)).mpr ⟨(hprime 0).1,hzero⟩
  exact ⟨rfl,walshTransfer_dihedral_nonsingular hN _ hm,hm⟩

theorem binary_factor_condition_iff {N : ℕ} (hN : 0 < N)
    {ι : Type} [Fintype ι] (hc : Fintype.card ι = 2)
    (f : Tensor AlgebraicComplex ι) :
    (f = 0 ∨ PrimeFactorsDihedralBinary N f) ↔ BinaryPhase N (walshCoordinates f) := by
  constructor
  · rintro (rfl | h)
    · rw [walsh_zero]
      exact ⟨hasParity_zero,fun _ => Or.inl ⟨rfl,rfl⟩⟩
    · exact binary_phase_of_prime_factors hN hc f h
  · intro h
    by_cases hf : f = 0
    · exact Or.inl hf
    · exact Or.inr (prime_factors_of_binary_phase hN hc f hf h)

/-- Literal condition (C), specialized only to quaternary input and hence
binary residual cards. Every actual positive prime factor, representative,
ordered port pair and native kernel orientation remains quantified. -/
def NativeDihedralFactorCondition (N : ℕ)
    (P R : AlgebraicComplex → AMat) (f : Signature AlgebraicComplex 4) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (s : AlgebraicComplex), Root N s →
    (card (nativeKernel (P s)) i j hij f = 0 ∨
      PrimeFactorsDihedralBinary N (card (nativeKernel (P s)) i j hij f)) ∧
    (card (nativeKernel (P s).transpose) i j hij f = 0 ∨
      PrimeFactorsDihedralBinary N (card (nativeKernel (P s).transpose) i j hij f)) ∧
    (card (nativeKernel (R s)) i j hij f = 0 ∨
      PrimeFactorsDihedralBinary N (card (nativeKernel (R s)) i j hij f)) ∧
    (card (nativeKernel (R s).transpose) i j hij f = 0 ∨
      PrimeFactorsDihedralBinary N (card (nativeKernel (R s).transpose) i j hij f))

theorem native_factor_condition_iff {N : ℕ} (hN : 0 < N)
    (P R : AlgebraicComplex → AMat) (f : Signature AlgebraicComplex 4) :
    NativeDihedralFactorCondition N P R f ↔ NativeDihedralContractions N P R f := by
  unfold NativeDihedralFactorCondition NativeDihedralContractions
  have hc (i j : Fin 4) (hij : i ≠ j) :
      Fintype.card (EndpointSelfLoop.Remaining i j) = 2 := by
    have hh := EndpointSelfLoop.remaining_card i j hij
    simp only [Fintype.card_fin] at hh
    omega
  constructor <;> intro h i j hij s hs
  · exact ⟨(binary_factor_condition_iff hN (hc i j hij) _).mp (h i j hij s hs).1,
      (binary_factor_condition_iff hN (hc i j hij) _).mp (h i j hij s hs).2.1,
      (binary_factor_condition_iff hN (hc i j hij) _).mp (h i j hij s hs).2.2.1,
      (binary_factor_condition_iff hN (hc i j hij) _).mp (h i j hij s hs).2.2.2⟩
  · exact ⟨(binary_factor_condition_iff hN (hc i j hij) _).mpr (h i j hij s hs).1,
      (binary_factor_condition_iff hN (hc i j hij) _).mpr (h i j hij s hs).2.1,
      (binary_factor_condition_iff hN (hc i j hij) _).mpr (h i j hij s hs).2.2.1,
      (binary_factor_condition_iff hN (hc i j hij) _).mpr (h i j hij s hs).2.2.2⟩

theorem source_5_13_conditionC {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (P R : AlgebraicComplex → AMat) (κ τ : AlgebraicComplex → AlgebraicComplex)
    (hκ : ∀ s, Root N s → κ s ≠ 0) (hτ : ∀ s, Root N s → τ s ≠ 0)
    (hP : ∀ s, Root N s → walshBinary (P s) = κ s • PhaseCards.plusKernel s)
    (hR : ∀ s, Root N s → walshBinary (R s) = τ s • reflectedBinary s)
    (f : Signature AlgebraicComplex 4) (hf : f ≠ 0) :
    NativeDihedralFactorCondition N P R f ↔
      HasParity (walshCoordinates f) ∧ DihedralNormalForm N (walshCoordinates f) ∧
        PhaseProduct N (walshCoordinates f) ∧
          ((complementaryPairs (walshCoordinates f)).card = 1 ∨
            (complementaryPairs (walshCoordinates f)).card = 2) :=
  (native_factor_condition_iff (by omega) P R f).trans
    (source_5_13_native hN hodd P R κ τ hκ hτ hP hR f hf)

theorem source_5_13_conditionC_prime_iff {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (P R : AlgebraicComplex → AMat) (κ τ : AlgebraicComplex → AlgebraicComplex)
    (hκ : ∀ s, Root N s → κ s ≠ 0) (hτ : ∀ s, Root N s → τ s ≠ 0)
    (hP : ∀ s, Root N s → walshBinary (P s) = κ s • PhaseCards.plusKernel s)
    (hR : ∀ s, Root N s → walshBinary (R s) = τ s • reflectedBinary s)
    (f : Signature AlgebraicComplex 4) (h : NativeDihedralFactorCondition N P R f) :
    TensorPrime f ↔ ∃ (a : Word4) (p δ : AlgebraicComplex),
      p ≠ 0 ∧ Root N δ ∧ walshCoordinates f = fun x => p * twoPoint a δ x :=
  source_5_13_native_prime_iff hN hodd P R κ τ hκ hτ hP hR f
    ((native_factor_condition_iff (by omega) P R f).mp h)

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity

