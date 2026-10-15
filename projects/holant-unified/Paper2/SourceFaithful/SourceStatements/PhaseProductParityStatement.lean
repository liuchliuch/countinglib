import Paper2.SourceFaithful.SourceStatements.PhaseProductParityRepresentatives
import Paper2.SourceFaithful.SourceStatements.PhaseProductParityNative
import Paper2.SourceFaithful.SourceStatements.PhaseProductParityBinaryShape
import Paper2.SourceFaithful.SourceStatements.PhaseProductParityPrime
import Paper2.SourceFaithful.SourceStatements.PhaseProductParitySupport
import Paper2.SourceFaithful.SourceStatements.PhaseProductContractionStatement

/-! Complete local source statements 5.12 and 5.13. The former is exported
as `source_5_12_representatives`, with its actual representative scales and
both directions. The latter has no group-safety, parity, support, factorisation
certificate, or accepted-proof-provider hypothesis. Its converse uses the
literal P_N partition contraction theorem, including cross-block cards. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup

theorem phaseProduct_local_dihedral {N : ℕ} (hN : 0 < N)
    {f : Signature AlgebraicComplex 4} (hf : PhaseProduct N f) :
    DihedralContractions N f := by
  intro i j hij u v s hs
  let r : rootsOfUnity N AlgebraicComplex :=
    ⟨Units.mk0 s (root_ne_zero hN hs),by
      rw [mem_rootsOfUnity]
      apply Units.ext
      simpa [Root] using hs⟩
  have ht := hf.card_xor r i j hij u v
  change PhaseProduct N (card (xorKernel u v s) i j hij f) at ht
  have hc : Fintype.card (EndpointSelfLoop.Remaining i j) = 2 := by
    have hh := EndpointSelfLoop.remaining_card i j hij
    simp only [Fintype.card_fin] at hh
    omega
  exact binary_phaseProduct hN hc _ ht

/-- Full converse of source Proposition 5.13, for every phase and both
reflection orientations. Oddness is needed only for its forward classification. -/
theorem source_5_13_converse {N : ℕ} (hN : 0 < N)
    {f : Signature AlgebraicComplex 4} (h : DihedralNormalForm N f) :
    DihedralContractions N f :=
  phaseProduct_local_dihedral hN (dihedral_normalForm_phaseProduct hN h)

/-- Exactly the two displayed source forms, one Walsh parity, literal P_N
membership, and one or two actual nonzero complementary support pairs. -/
theorem source_5_13 {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (f : Signature AlgebraicComplex 4) (hf : f ≠ 0) :
    DihedralContractions N f ↔
      HasParity f ∧ DihedralNormalForm N f ∧ PhaseProduct N f ∧
        ((complementaryPairs f).card = 1 ∨ (complementaryPairs f).card = 2) := by
  constructor
  · intro h
    have hform := local_dihedral_normalForm hN hodd f hf h
    exact ⟨((local_dihedral_iff hN f).mp h).1,hform,
      dihedral_normalForm_phaseProduct (by omega) hform,
      normalForm_pair_count (by omega) hform⟩
  · rintro ⟨_,hform,_,_⟩
    exact source_5_13_converse (by omega) hform

/-- Including the zero table, P_N is exactly the complete local four-port
phase/reflection contraction class at odd order. -/
theorem source_5_13_phaseProduct_iff {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (f : Signature AlgebraicComplex 4) :
    DihedralContractions N f ↔ PhaseProduct N f :=
  ⟨source_5_13_phaseProduct hN hodd f,phaseProduct_local_dihedral (by omega)⟩

/-- The prime characterization includes the converse for every genuine
positive ordered tensor cut; no selected factorisation is assumed. -/
theorem source_5_13_prime_iff {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (f : Signature AlgebraicComplex 4) (h : DihedralContractions N f) :
    TensorPrime f ↔ ∃ (a : Word4) (p δ : AlgebraicComplex),
      p ≠ 0 ∧ Root N δ ∧ f = fun x => p * twoPoint a δ x := by
  constructor
  · exact fun hp => source_5_13_prime_forward hN hodd f hp h
  · rintro ⟨a,p,δ,hp,hδ,rfl⟩
    exact source_5_13_prime_converse a p δ hp (root_ne_zero (by omega) hδ)

lemma walshCoordinates_ne_zero {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : f ≠ 0) : walshCoordinates f ≠ 0 := by
  intro hz
  apply hf
  exact (Conformal.action_eq_zero_iff walshBasis.symm f).mp
    (by simpa only [walshBasis_inverse_action] using hz)

/-- Proposition 5.13 on the original tensor and its specified nonzero
rotation/reflection representatives. Every native card and its reverse
orientation is tested; the conclusion is the literal Walsh table. -/
theorem source_5_13_native {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (P R : AlgebraicComplex → AMat) (κ τ : AlgebraicComplex → AlgebraicComplex)
    (hκ : ∀ s, Root N s → κ s ≠ 0) (hτ : ∀ s, Root N s → τ s ≠ 0)
    (hP : ∀ s, Root N s → walshBinary (P s) = κ s • PhaseCards.plusKernel s)
    (hR : ∀ s, Root N s → walshBinary (R s) = τ s • reflectedBinary s)
    (f : Signature AlgebraicComplex 4) (hf : f ≠ 0) :
    NativeDihedralContractions N P R f ↔
      HasParity (walshCoordinates f) ∧ DihedralNormalForm N (walshCoordinates f) ∧
        PhaseProduct N (walshCoordinates f) ∧
          ((complementaryPairs (walshCoordinates f)).card = 1 ∨
            (complementaryPairs (walshCoordinates f)).card = 2) := by
  rw [native_dihedral_iff (by omega) P R κ τ hκ hτ hP hR f]
  exact source_5_13 hN hodd _ (walshCoordinates_ne_zero hf)

/-- The original tensor is prime exactly when its Walsh table has the
one-pair form. Tensor primeness is transported across the actual invertible
Walsh matrix for every ordered tensor cut. -/
theorem source_5_13_native_prime_iff {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (P R : AlgebraicComplex → AMat) (κ τ : AlgebraicComplex → AlgebraicComplex)
    (hκ : ∀ s, Root N s → κ s ≠ 0) (hτ : ∀ s, Root N s → τ s ≠ 0)
    (hP : ∀ s, Root N s → walshBinary (P s) = κ s • PhaseCards.plusKernel s)
    (hR : ∀ s, Root N s → walshBinary (R s) = τ s • reflectedBinary s)
    (f : Signature AlgebraicComplex 4) (h : NativeDihedralContractions N P R f) :
    TensorPrime f ↔ ∃ (a : Word4) (p δ : AlgebraicComplex),
      p ≠ 0 ∧ Root N δ ∧ walshCoordinates f = fun x => p * twoPoint a δ x := by
  have ht := (native_dihedral_iff (by omega) P R κ τ hκ hτ hP hR f).mp h
  have hp := tensorPrime_action_iff walshBasis.symm f
  rw [walshBasis_inverse_action] at hp
  exact hp.symm.trans (source_5_13_prime_iff hN hodd _ ht)

theorem cyclic_live_ratio {N : ℕ} {p t : AlgebraicComplex}
    {x y : Fin 3 → AlgebraicComplex} (hp : p ≠ 0)
    (h : CyclicNormalForm N p t x y) :
    Root N (t / p) ∧ ∀ i, (x i = 0 ∧ y i = 0) ∨
      ∃ α, Root N α ∧ x i = -p * (t / p) / α ∧ y i = -p * α := by
  rcases h with ⟨_,_,lambda,hlambda,ht,hpairs⟩ | ⟨hz,_,_⟩
  · have he : t / p = lambda := by rw [ht]; field_simp
    simpa only [he] using And.intro hlambda hpairs
  · exact False.elim (hp hz)

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity

