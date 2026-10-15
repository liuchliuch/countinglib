import Paper2.SourceFaithful.SourceStatements.PhaseProductParityRepresentatives
import Paper2.SourceFaithful.SourceStatements.PhaseProductParityTransfer

/-! Source Lemma 5.12 with its literal zero-or-nonsingular cyclic transfer
membership condition. Residual binary tensors are enumerated only to form
their actual coefficient matrices; all ordered surviving ports are retained. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup TypeParityStatement
set_option backward.isDefEq.respectTransparency false

def binaryPortOrder {ι : Type} [Fintype ι] (hc : Fintype.card ι = 2) : ι ≃ Fin 2 :=
  (Fintype.equivFin ι).trans (finCongr hc)

def CyclicBinaryPhase {ι : Type} [Fintype ι] (N : ℕ)
    (f : Tensor AlgebraicComplex ι) : Prop :=
  SupportedOnParity f 0 ∧ ∀ x, RootComplement N (f x) (f (fun i => !(x i)))

lemma CyclicBinaryPhase.reindex {N : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    {f : Tensor AlgebraicComplex ι} (hf : CyclicBinaryPhase N f) (e : ι ≃ κ) :
    CyclicBinaryPhase N (Tensor.reindex e f) :=
  ⟨supportedOnParity_reindex e f 0 hf.1,fun x => hf.2 (fun i => x (e i))⟩

theorem cyclic_binary_literal_iff_order {N : ℕ} (hN : 0 < N)
    {ι : Type} [Fintype ι] (e : ι ≃ Fin 2) (f : Tensor AlgebraicComplex ι) :
    (f = 0 ∨
      (tableBinary (Tensor.reindex e f)).det ≠ 0 ∧
        WalshTransferMember .cyclic N (tableBinary (Tensor.reindex e f))) ↔
      CyclicBinaryPhase N (walshCoordinates f) := by
  classical
  have hcanc : Tensor.reindex e.symm (Tensor.reindex e (walshCoordinates f)) =
      walshCoordinates f := by simp
  constructor
  · rintro (rfl | ⟨_,hm⟩)
    · rw [walsh_zero]
      exact ⟨fun _ hn => False.elim (hn rfl),fun _ => Or.inl ⟨rfl,rfl⟩⟩
    · have hh := (walshTransfer_cyclic_iff hN (Tensor.reindex e f)).mp hm
      have hp : CyclicBinaryPhase N (walshCoordinates (Tensor.reindex e f)) := hh.2
      rw [walshCoordinates_reindex] at hp
      have hi := hp.reindex e.symm
      rw [hcanc] at hi
      exact hi
  · intro hp
    by_cases hf : f = 0
    · exact Or.inl hf
    · have hg : Tensor.reindex e f ≠ 0 := by
        intro hz
        apply hf
        have hh := congrArg (Tensor.reindex e.symm) hz
        change Tensor.reindex e.symm (Tensor.reindex e f) = 0 at hh
        simpa using hh
      have hh := hp.reindex e
      rw [← walshCoordinates_reindex] at hh
      have hm := (walshTransfer_cyclic_iff hN (Tensor.reindex e f)).mpr ⟨hg,hh⟩
      exact Or.inr ⟨walshTransfer_cyclic_nonsingular hN _ hm,hm⟩

theorem cyclic_binary_literal_iff {N : ℕ} (hN : 0 < N)
    {ι : Type} [Fintype ι] (hc : Fintype.card ι = 2) (f : Tensor AlgebraicComplex ι) :
    (f = 0 ∨
      (tableBinary (Tensor.reindex (binaryPortOrder hc) f)).det ≠ 0 ∧
        WalshTransferMember .cyclic N (tableBinary (Tensor.reindex (binaryPortOrder hc) f))) ↔
      CyclicBinaryPhase N (walshCoordinates f) :=
  cyclic_binary_literal_iff_order hN (binaryPortOrder hc) f

lemma remaining_two (i j : Fin 4) (hij : i ≠ j) :
    Fintype.card (EndpointSelfLoop.Remaining i j) = 2 := by
  have hh := EndpointSelfLoop.remaining_card i j hij
  simp only [Fintype.card_fin] at hh
  omega

/-- The source's literal whole-contraction test, not a coordinate-level
surrogate. Every card is zero or has nonzero determinant and actual cyclic
Walsh transfer membership. -/
def LiteralCyclicContractions (N : ℕ) (B : AlgebraicComplex → AMat)
    (f : Signature AlgebraicComplex 4) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (s : AlgebraicComplex), Root N s →
    ∀ e : EndpointSelfLoop.Remaining i j ≃ Fin 2,
    card (nativeKernel (B s)) i j hij f = 0 ∨
      (tableBinary (Tensor.reindex e
        (card (nativeKernel (B s)) i j hij f))).det ≠ 0 ∧
      WalshTransferMember .cyclic N
        (tableBinary (Tensor.reindex e
          (card (nativeKernel (B s)) i j hij f)))

theorem literal_cyclic_iff {N : ℕ} (hN : 0 < N) (B : AlgebraicComplex → AMat)
    (f : Signature AlgebraicComplex 4) :
    LiteralCyclicContractions N B f ↔ NativeCyclicContractions N B f := by
  unfold LiteralCyclicContractions NativeCyclicContractions
  constructor <;> intro h i j hij s hs
  · exact (cyclic_binary_literal_iff hN (remaining_two i j hij) _).mp
      (h i j hij s hs (binaryPortOrder (remaining_two i j hij)))
  · intro e
    exact (cyclic_binary_literal_iff_order hN e _).mpr (h i j hij s hs)

/-- Full original source 5.12, including its converse and its literal
nonsingular group-membership hypothesis on each actual native contraction. -/
theorem source_5_12_literal {N : ℕ} (hN : 3 ≤ N)
    (B : AlgebraicComplex → AMat) (κ : AlgebraicComplex → AlgebraicComplex)
    (hκ : ∀ s, Root N s → κ s ≠ 0)
    (hB : ∀ s, Root N s → walshBinary (B s) = κ s • PhaseCards.plusKernel s)
    (f : Signature AlgebraicComplex 4)
    (heven : SupportedOnParity (walshCoordinates f) 0) :
    LiteralCyclicContractions N B f ↔
      CyclicNormalForm N (walshCoordinates f (fun _ => false))
        (walshCoordinates f (fun _ => true))
        (fun i => walshCoordinates f (centralWord i (fun _ => false)))
        (fun i => walshCoordinates f (flipAll (centralWord i (fun _ => false)))) :=
  (literal_cyclic_iff (by omega) B f).trans (source_5_12_native hN B κ hκ hB f heven)

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity

