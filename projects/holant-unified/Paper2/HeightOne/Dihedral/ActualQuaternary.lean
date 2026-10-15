import Paper2.HeightOne.Dihedral.BinaryComplement
import Paper2.HeightOne.Dihedral.QuaternaryProduct
import Paper2.HeightOne.PhaseCards.OrientedCards

/-! The actual odd-dihedral four-port theorem. Every RN pencil is derived
from an actual phase/reflection network and its precise nonzero Walsh scale.
No RN deck, support certificate or desired classification is a premise. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Tractable PhasePencil PhaseCards GroupSplit GroupSplit.MatrixGroup EndpointSelfLoop

lemma RootComplement.safe {N : ℕ} {p q : AlgebraicComplex}
    (h : RootComplement N p q) :
    (p = 0 ∧ q = 0) ∨ ∃ η κ, Root N η ∧ κ ≠ 0 ∧ p = κ ∧ q = -κ * η := by
  rcases h with h | ⟨r, hr, hp, hq⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, p, hr, hp, rfl, by rw [hq]; ring⟩

lemma actual_two_port_rootComplement {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hN : 0 < N) (hG : actualClasses F = dihedralPhaseClasses N)
    (hsafe : AllBinariesSafe F) {ι : Type} [Fintype ι]
    (hcard : Fintype.card ι = 2) (f : Tensor AlgebraicComplex ι)
    (hf : NetworkRealizable F f) (x : ι → Bool) :
    RootComplement N (walshCoordinates f x) (walshCoordinates f (fun j => !(x j))) := by
  let e : Fin 2 ≃ ι := (finCongr hcard.symm).trans (Fintype.equivFin ι).symm
  let g := Tensor.reindex e.symm f
  have hg := actual_binary_rootComplement hN hG hsafe g (hf.reindex e.symm) (fun j => x (e j))
  simpa only [g, walshCoordinates_reindex, Tensor.reindex_apply, Equiv.apply_symm_apply] using hg

lemma actual_two_port_hasParity {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = dihedralPhaseClasses N) (hsafe : AllBinariesSafe F)
    {ι : Type} [Fintype ι] (hcard : Fintype.card ι = 2)
    (f : Tensor AlgebraicComplex ι) (hf : NetworkRealizable F f) :
    HasParity (walshCoordinates f) := by
  classical
  let e : Fin 2 ≃ ι := (finCongr hcard.symm).trans (Fintype.equivFin ι).symm
  let g := Tensor.reindex e.symm f
  have hg : HasParity (walshCoordinates g) := by
    by_cases hz : g = 0
    · rw [hz, walsh_zero]
      exact hasParity_zero
    have hp := normalized_binary_hasParity (Or.inr hG)
      (actual_tableBinary hsafe g (hf.reindex e.symm) hz)
    rwa [binarySignature_tableBinary] at hp
  have hp := hasParity_reindex e (walshCoordinates g) hg
  convert hp using 1
  funext x
  simp only [g, walshCoordinates_reindex, Tensor.reindex_apply,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Exact complementary coefficient relation for each actual oriented xor
card. The surviving port order is retained via a true finite equivalence. -/
theorem actual_xor_contraction_rootComplement
    {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hN : 0 < N) (hG : actualClasses F = dihedralPhaseClasses N)
    (hsafe : AllBinariesSafe F) (f : Signature AlgebraicComplex 4)
    (hf : NetworkRealizable F f) (i j : Fin 4) (hij : i ≠ j)
    (u v : Bool) (s : AlgebraicComplex) (hs : Root N s)
    (x : Remaining i j → Bool) :
    RootComplement N
      (card (xorKernel u v s) i j hij (walshCoordinates f) x)
      (card (xorKernel u v s) i j hij (walshCoordinates f) (fun k => !(x k))) := by
  obtain ⟨B, c, hB, hc, he⟩ := actual_xor_card hN hG u v s hs
  let g := card (nativeKernel B) i j hij f
  have hg : NetworkRealizable F g :=
    actual_contractKernel (hf.reindex (splitPorts i j hij)) hB.1
  have harity : Fintype.card (Remaining i j) = 2 := by
    have h := remaining_card i j hij
    simp only [Fintype.card_fin] at h
    omega
  have hcomp := actual_two_port_rootComplement hN hG hsafe harity g hg x
  have hwalsh : walshCoordinates g =
      c • card (xorKernel u v s) i j hij (walshCoordinates f) := by
    dsimp only [g]
    rw [walshCoordinates_card]
    change card (analysisKernel B) i j hij (walshCoordinates f) = _
    rw [he]
    unfold card
    rw [contractKernel_scale]
  rw [hwalsh] at hcomp
  exact (RootComplement.smul_iff _ _ _ hc).mp hcomp

lemma extendBits_flipPair (i j : Fin 4) (hij : i ≠ j) (a : Word4) :
    extendBits i j hij (restrict i j a) (!(a i)) (!(a j)) = flipPair i j a := by
  classical
  funext k
  by_cases hki : k = i
  · subst k
    simp [extendBits, splitPorts, flipPair]
  by_cases hkj : k = j
  · subst k
    simp [extendBits, splitPorts, flipPair, hij, Ne.symm hij]
  · simp [extendBits, splitPorts, flipPair, restrict, hki, hkj]

lemma extendBits_flipRemaining (i j : Fin 4) (hij : i ≠ j) (a : Word4) :
    extendBits i j hij (fun k => !(restrict i j a k)) (a i) (a j) =
      flipAll (flipPair i j a) := by
  classical
  funext k
  by_cases hki : k = i
  · subst k
    simp [extendBits, splitPorts, flipPair, flipAll]
  by_cases hkj : k = j
  · subst k
    simp [extendBits, splitPorts, flipPair, flipAll, hij, Ne.symm hij]
  · simp [extendBits, splitPorts, flipPair, flipAll, restrict, hki, hkj]

lemma extendBits_flipAll (i j : Fin 4) (hij : i ≠ j) (a : Word4) :
    extendBits i j hij (fun k => !(restrict i j a k)) (!(a i)) (!(a j)) = flipAll a := by
  classical
  funext k
  by_cases hki : k = i
  · subst k
    simp [extendBits, splitPorts, flipAll]
  by_cases hkj : k = j
  · subst k
    simp [extendBits, splitPorts, flipAll, hij, Ne.symm hij]
  · simp [extendBits, splitPorts, flipAll, restrict, hki, hkj]

/-- Every ordered pair and every base word has the complete RN relation,
proved using actual binary gadgets and the exact Paper 1 pencil lemma. -/
theorem actual_quaternary_fullDeck (P : Paper1PhasePencilAccepted)
    {F : SignatureFamily AlgebraicComplex} {N : ℕ} (hN : 3 ≤ N)
    (hG : actualClasses F = dihedralPhaseClasses N) (hsafe : AllBinariesSafe F)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f) :
    FullQuaternaryDeck N (walshCoordinates f) := by
  intro i j hij a
  apply (P.phasePencil_7_1 N hN _ _ _ _).mpr
  intro s hs
  have h := actual_xor_contraction_rootComplement (by omega) hG hsafe f hf
    i j hij (a i) (a j) s hs (restrict i j a)
  rw [card_xor_apply, card_xor_apply, extendBits_restrict, extendBits_flipPair,
    extendBits_flipRemaining, extendBits_flipAll] at h
  exact h.safe

/-- One Walsh parity of an actual four-port signature follows from the
complete actual binary group. The parity is not a classification hypothesis. -/
theorem actual_quaternary_walsh_hasParity
    {F : SignatureFamily AlgebraicComplex} {N : ℕ} (hN : 3 ≤ N)
    (hG : actualClasses F = dihedralPhaseClasses N) (hsafe : AllBinariesSafe F)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f) :
    HasParity (walshCoordinates f) := by
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := exists_algebraic_primitiveRoot N (by omega)
  apply hasParity_of_root_of_unity_contractions (by simp) N hN ζ hζ
  intro i j hij s hs
  let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
  obtain ⟨B, c, hB, hc, he⟩ := actual_plus_card (Or.inr hG) r
  let g := card (nativeKernel B) i j hij f
  have hg : NetworkRealizable F g :=
    actual_contractKernel (hf.reindex (splitPorts i j hij)) hB.1
  have harity : Fintype.card (Remaining i j) = 2 := by
    have h := remaining_card i j hij
    simp only [Fintype.card_fin] at h
    omega
  have hp := actual_two_port_hasParity hG hsafe harity g hg
  have hw : walshCoordinates g = (2 * c) • plusContraction i j hij s (walshCoordinates f) := by
    dsimp only [g]
    rw [walshCoordinates_card]
    change card (analysisKernel B) i j hij (walshCoordinates f) = _
    have he' : analysisKernel B = (2 * c) • PhaseCards.plusKernel s := by
      simpa only [r, rootsOfUnity.coe_mkOfPowEq] using he
    rw [he']
    unfold card
    rw [contractKernel_scale]
    congr 1
    exact card_plus s i j hij _
  rw [hw] at hp
  exact (hasParity_scale_iff _ (mul_ne_zero (by norm_num) hc) _).mp hp

/-- The source dihedral quaternary proposition's actual Product conclusion, with the complete
RN deck and Walsh parity both discharged from real network semantics. -/
theorem actual_quaternary_walsh_product (P : Paper1PhasePencilAccepted)
    {F : SignatureFamily AlgebraicComplex} {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (hG : actualClasses F = dihedralPhaseClasses N) (hsafe : AllBinariesSafe F)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f) :
    Product (walshCoordinates f) :=
  quaternary_product_of_fullDeck hodd
    (actual_quaternary_walsh_hasParity hN hG hsafe f hf)
    (actual_quaternary_fullDeck P hN hG hsafe f hf)

end
end Paper2.HeightOne.Dihedral

