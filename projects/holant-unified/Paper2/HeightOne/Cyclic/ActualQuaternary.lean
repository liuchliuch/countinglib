import Paper2.HeightOne.Dihedral.ActualQuaternary
import Paper2.HeightOne.Cyclic.DressingPhases

/-! The cyclic four-port phase deck derived from actual binary networks.
Only equal-bit kernels are used: the reflected odd-dihedral deck is neither
assumed nor inferred for a cyclic group. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhasePencil PhaseCards GroupSplit GroupSplit.MatrixGroup EndpointSelfLoop
open Dihedral
open GroupSplit.FiniteGroupFacts.ProjectiveCentralizers

theorem actual_binary_cyclic_shape {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N) {B : AMat}
    (hB : ActualNonsingular F B) :
    ∃ (s : rootsOfUnity N AlgebraicComplex) (c : AlgebraicComplex),
      c ≠ 0 ∧ transfer B = c • phase s.val := by
  obtain ⟨U, hU, hu⟩ := actual_transfer_GL hB
  rw [hG] at hu
  obtain ⟨s, hs, he⟩ := hu
  have he' := pglMk_eq_iff_projectiveClass_eq.mp he.symm
  rw [hU] at he'
  obtain ⟨c, hc, hm⟩ := projectiveClass_eq_iff.mp he'
  exact ⟨⟨s, hs⟩, c, hc, hm⟩

theorem actual_binary_cyclic_rootComplement
    {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hN : 0 < N) (hG : actualClasses F = cyclicPhaseClasses N)
    (hsafe : AllBinariesSafe F) (f : Signature AlgebraicComplex 2)
    (hf : NetworkRealizable F f) (x : Fin 2 → Bool) :
    RootComplement N (walshCoordinates f x) (walshCoordinates f (fun j => !(x j))) := by
  by_cases hz : f = 0
  · rw [hz, walsh_zero]
    exact Or.inl ⟨rfl, rfl⟩
  have hB := actual_tableBinary hsafe f hf hz
  obtain ⟨s, c, hc, hs⟩ := actual_binary_cyclic_shape hG hB
  rw [← binarySignature_tableBinary f, walshCoordinates_binary, rotation_walsh_binary hs]
  change RootComplement N ((c / 2) * plusKernel (s.val : AlgebraicComplex) (x 0) (x 1))
    ((c / 2) * plusKernel (s.val : AlgebraicComplex) (!(x 0)) (!(x 1)))
  exact (RootComplement.smul_iff _ _ _ (div_ne_zero hc (by norm_num))).mpr
    (plusKernel_rootComplement hN _ (root_of_unity s) _ _)

lemma actual_cyclic_two_port_rootComplement
    {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hN : 0 < N) (hG : actualClasses F = cyclicPhaseClasses N)
    (hsafe : AllBinariesSafe F) {ι : Type} [Fintype ι]
    (hcard : Fintype.card ι = 2) (f : Tensor AlgebraicComplex ι)
    (hf : NetworkRealizable F f) (x : ι → Bool) :
    RootComplement N (walshCoordinates f x) (walshCoordinates f (fun j => !(x j))) := by
  let e : Fin 2 ≃ ι := (finCongr hcard.symm).trans (Fintype.equivFin ι).symm
  let g := Tensor.reindex e.symm f
  have hg := actual_binary_cyclic_rootComplement hN hG hsafe g
    (hf.reindex e.symm) (fun j => x (e j))
  simpa only [g, walshCoordinates_reindex, Tensor.reindex_apply,
    Equiv.apply_symm_apply] using hg

lemma actual_cyclic_two_port_even
    {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N) (hsafe : AllBinariesSafe F)
    {ι : Type} [Fintype ι] (hcard : Fintype.card ι = 2)
    (f : Tensor AlgebraicComplex ι) (hf : NetworkRealizable F f) :
    SupportedOnParity (walshCoordinates f) 0 := by
  classical
  let e : Fin 2 ≃ ι := (finCongr hcard.symm).trans (Fintype.equivFin ι).symm
  let g := Tensor.reindex e.symm f
  have hg : SupportedOnParity (walshCoordinates g) 0 := by
    by_cases hz : g = 0
    · rw [hz, walsh_zero]
      intro x hx
      exact False.elim (hx rfl)
    have hp := cyclic_binary_even hG (actual_tableBinary hsafe g (hf.reindex e.symm) hz)
    rwa [binarySignature_tableBinary] at hp
  have hp := supportedOnParity_reindex e (walshCoordinates g) 0 hg
  convert hp using 1
  funext x
  simp only [g, walshCoordinates_reindex, Tensor.reindex_apply,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Every actual phase contraction obeys the complementary coefficient law,
including zero contractions and its exact nonzero representative scale. -/
theorem actual_plus_contraction_rootComplement
    {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hN : 0 < N) (hG : actualClasses F = cyclicPhaseClasses N)
    (hsafe : AllBinariesSafe F) (f : Signature AlgebraicComplex 4)
    (hf : NetworkRealizable F f) (i j : Fin 4) (hij : i ≠ j)
    (s : AlgebraicComplex) (hs : Root N s) (x : Remaining i j → Bool) :
    RootComplement N
      (plusContraction i j hij s (walshCoordinates f) x)
      (plusContraction i j hij s (walshCoordinates f) (fun k => !(x k))) := by
  letI : NeZero N := ⟨by omega⟩
  let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
  obtain ⟨B, c, hB, hc, he⟩ := actual_plus_card (Or.inl hG) r
  let g := card (nativeKernel B) i j hij f
  have hg : NetworkRealizable F g :=
    actual_contractKernel (hf.reindex (splitPorts i j hij)) hB.1
  have harity : Fintype.card (Remaining i j) = 2 := by
    have h := remaining_card i j hij
    simp only [Fintype.card_fin] at h
    omega
  have hcomp := actual_cyclic_two_port_rootComplement hN hG hsafe harity g hg x
  have hw : walshCoordinates g =
      (2 * c) • plusContraction i j hij s (walshCoordinates f) := by
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
  rw [hw] at hcomp
  exact (RootComplement.smul_iff _ _ _ (mul_ne_zero (by norm_num) hc)).mp hcomp

/-- The shared cyclic quaternary RN rows.  The reverse row comes from
contracting the complementary named pair, preserving all six ordered sectors. -/
theorem actual_cyclic_quaternary_relations (P : Paper1PhasePencilAccepted)
    {F : SignatureFamily AlgebraicComplex} {N : ℕ} (hN : 3 ≤ N)
    (hG : actualClasses F = cyclicPhaseClasses N) (hsafe : AllBinariesSafe F)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f) :
    ∀ i : Fin 3,
      Relation N (walshCoordinates f (fun _ => false))
        (walshCoordinates f (centralWord i (fun _ => false)))
        (walshCoordinates f (flipAll (centralWord i (fun _ => false))))
        (walshCoordinates f (fun _ => true)) ∧
      Relation N (walshCoordinates f (fun _ => false))
        (walshCoordinates f (flipAll (centralWord i (fun _ => false))))
        (walshCoordinates f (centralWord i (fun _ => false)))
        (walshCoordinates f (fun _ => true)) := by
  have row (i j : Fin 4) (hij : i ≠ j) :
      Relation N (walshCoordinates f (fun _ => false))
        (walshCoordinates f (flipPair i j (fun _ => false)))
        (walshCoordinates f (flipAll (flipPair i j (fun _ => false))))
        (walshCoordinates f (fun _ => true)) := by
    apply (P.phasePencil_7_1 N hN _ _ _ _).mpr
    intro s hs
    have h := actual_plus_contraction_rootComplement (by omega) hG hsafe f hf
      i j hij s hs (restrict i j (fun _ => false))
    simp only [← card_plus s i j hij _, ← xorKernel_false_false,
      card_xor_apply, extendBits_restrict, extendBits_flipPair,
      extendBits_flipRemaining, extendBits_flipAll] at h
    exact h.safe
  intro i
  constructor
  · exact row 0 i.succ (by intro he; have := congrArg Fin.val he; simp at this)
  · simpa only [flip_other_pair, flipAll_flipAll] using
      row (otherFirst i) (otherSecond i) (other_distinct i)

/-- Even Walsh support is proved from the actual cyclic phase cards. -/
theorem actual_cyclic_quaternary_even
    {F : SignatureFamily AlgebraicComplex} {N : ℕ} (hN : 3 ≤ N)
    (hG : actualClasses F = cyclicPhaseClasses N) (hsafe : AllBinariesSafe F)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f) :
    SupportedOnParity (walshCoordinates f) 0 := by
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := exists_algebraic_primitiveRoot N (by omega)
  apply even_of_root_of_unity_contractions (by simp) N (by omega) ζ hζ
  intro i j hij s hs
  let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
  obtain ⟨B, c, hB, hc, he⟩ := actual_plus_card (Or.inl hG) r
  let g := card (nativeKernel B) i j hij f
  have hg : NetworkRealizable F g :=
    actual_contractKernel (hf.reindex (splitPorts i j hij)) hB.1
  have harity : Fintype.card (Remaining i j) = 2 := by
    have h := remaining_card i j hij
    simp only [Fintype.card_fin] at h
    omega
  have hp := actual_cyclic_two_port_even hG hsafe harity g hg
  have hw : walshCoordinates g =
      (2 * c) • plusContraction i j hij s (walshCoordinates f) := by
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
  exact (supportedOnParity_scale_iff _ (mul_ne_zero (by norm_num) hc) _ 0).mp hp

end
end Paper2.HeightOne.Cyclic
