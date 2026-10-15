import Paper2.SourceFaithful.HeightOneProgress

/-! Real normalized successor stages, with the exact actual representatives
which the analytic cyclic and dihedral decks consume. The complete menu is
joined with those representatives before saturation, so no projective scaling
or arbitrary selected-factor choice is mistaken for literal membership. -/
namespace Paper2.SourceFaithful.HeightOne
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Tractable ExactInput
open Paper2.HeightOne Paper2.HeightOne.PhaseCards Paper2.HeightOne.Cyclic
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

def rotationMenuOf {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (C : RotationCards F N) (hN : 3 ≤ N) : BinaryMenu F := by
  letI : NeZero N := ⟨by omega⟩
  exact rotationMenu C

def xorMenuOf {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (C : XorCards F N) (hN : 3 ≤ N) : BinaryMenu F := by
  letI : NeZero N := ⟨by omega⟩
  exact xorMenu C

structure StableNormalizedStage (L : Language) where
  base : Language
  language : Language
  basis : InvertibleKernel
  a : AlgebraicComplex
  b : AlgebraicComplex
  diagonal : basis.matrix = diagonalKernel a b
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  conformal : XConformal basis
  N : ℕ
  order_ge_three : 3 ≤ N
  odd_order : Odd N
  group : actualClasses language.family = cyclicPhaseClasses N ∨
    actualClasses language.family = dihedralPhaseClasses N
  base_group : actualClasses language.family = actualClasses base.family
  retained : SourceRetainedExtension base language
  factorClosed : FactorClosed language.family
  even : ∀ f ∈ language.family, Even f.1
  safe : AllBinariesSafe language.family
  minArity : ℕ
  least : LeastPrimeArity language.family minArity
  rotations : RotationCards base.family N
  rotations_processed : ∀ f ∈ language.family,
    (rotationMenuOf rotations order_ge_three).Processed f language
  xor_cards : actualClasses language.family = dihedralPhaseClasses N →
    ∃ X : XorCards base.family N, ∀ f ∈ language.family,
      (xorMenuOf X order_ge_three).Processed f language
  field : ∀ f ∈ language.family, PullbackOver (originalField L) basis f
  original_subset : familyAction basis L.family ⊆ language.family
  backward : FixedFieldOutput.Reduces .nativeX language L
  forward : FixedFieldOutput.Reduces .nativeX L language

namespace StableNormalizedStage

lemma terminal {L : Language} (S : StableNormalizedStage L) (h : Terminal S.language) : Terminal L := by
  rcases h with ht | hh
  · left
    apply (xConformal_tract_iff S.conformal L.family).mpr
    exact ht.mono_family (familyAction_mono sourceKBasis S.original_subset)
  · exact Or.inr (hh.transport S.backward)

end StableNormalizedStage

private theorem stable_package
    {L : Language} (S : PrimeStage L) (D : InvertibleKernel)
    (a b : AlgebraicComplex) (hD : D.matrix = diagonalKernel a b)
    (ha : a ≠ 0) (hb : b ≠ 0) (hconf : XConformal D)
    (M B : Language) (hM : M.family = familyAction D S.language.family)
    (hML : FixedFieldOutput.Reduces .nativeX M S.language)
    (hLM : FixedFieldOutput.Reduces .nativeX S.language M)
    (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (hgroup : actualClasses M.family = cyclicPhaseClasses N ∨
      actualClasses M.family = dihedralPhaseClasses N)
    (menu : BinaryMenu M.family) (hB : SaturatedStage M B menu (originalField L) D)
    (hmin : LeastPrimeArity B.family S.minArity)
    (heq : actualClasses B.family = actualClasses M.family)
    (C : RotationCards M.family N)
    (hrot : ∀ f ∈ B.family, (rotationMenuOf C hN).Processed f B)
    (hxor : actualClasses B.family = dihedralPhaseClasses N →
      ∃ X : XorCards M.family N, ∀ f ∈ B.family, (xorMenuOf X hN).Processed f B) :
    Nonempty (StableNormalizedStage L) := by
  have hsub : familyAction D L.family ⊆ B.family := by
    have h := familyAction_mono D S.retained.subset
    rw [← hM] at h
    exact h.trans hB.retained.subset
  exact ⟨⟨M,B,D,a,b,hD,ha,hb,hconf,N,hN,hodd,
    by rw [heq]; exact hgroup,heq,hB.retained,hB.factorClosed,hB.even,hB.safe,
    S.minArity,hmin,C,hrot,hxor,hB.field,hsub,
    hB.retained.backward.trans (hML.trans S.retained.backward),
    S.retained.forward.trans (hLM.trans hB.retained.forward)⟩⟩

/-- Both odd-group cases choose actual analytic representatives, combine them
with a complete actual group menu, and really saturate that finite menu.
Every nonstable alternative is a canonical terminal or a strict actual stage. -/
theorem normalized_stage_step
    (P1 : GroupSplit.Paper1Accepted)
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (PU : Paper1UnaryAccepted)
    (PI : Paper1BinaryInterpolationAccepted) (PO : Paper1OddAccepted)
    (PN : Paper1NormalizationAccepted) {L : Language} (S : PrimeStage L)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hconf : XConformal D) (M : Language)
    (hM : M.family = familyAction D S.language.family)
    (hML : FixedFieldOutput.Reduces .nativeX M S.language)
    (hLM : FixedFieldOutput.Reduces .nativeX S.language M)
    (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (hgroup : actualClasses M.family = cyclicPhaseClasses N ∨
      actualClasses M.family = dihedralPhaseClasses N)
    (hsafe : AllBinariesSafe M.family) :
    Terminal L ∨ (∃ T : PrimeStage L, T.measure < S.measure) ∨
      Nonempty (StableNormalizedStage L) := by
  classical
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨C⟩ := rotationCards_nonempty hgroup
  have hbinary : ∃ B : AMat, ActualNonsingular M.family B := by
    rw [hM]
    exact actual_binary_diagonal S.binary D a b hD ha hb
  obtain ⟨complete,hcomplete⟩ := complete_binaryMenu (safe_classes_finite P1 M hsafe hbinary)
  by_cases hd : actualClasses M.family = dihedralPhaseClasses N
  · obtain ⟨X⟩ := xorCards_nonempty (by omega) hd
    let menu := complete.append ((rotationMenu C).append (xorMenu X))
    rcases normalized_saturation_progress P1 PG PR PF PU PI PO PN S D a b hD ha hb hconf
      M hM hML hLM menu with ht | hnext | ⟨B,hB,hmin,heq⟩
    · exact Or.inl ht
    · exact Or.inr (Or.inl hnext)
    · right
      right
      apply stable_package S D a b hD ha hb hconf M B hM hML hLM N hN hodd hgroup menu hB hmin heq C
      · intro f hf
        change (rotationMenu C).Processed f B
        exact BinaryMenu.Processed.left _ _ (BinaryMenu.Processed.right _ _ (hB.processed f hf))
      · intro _
        refine ⟨X, ?_⟩
        intro f hf
        change (xorMenu X).Processed f B
        exact BinaryMenu.Processed.right _ _ (BinaryMenu.Processed.right _ _ (hB.processed f hf))
  · have hc : actualClasses M.family = cyclicPhaseClasses N := hgroup.resolve_right hd
    let menu := complete.append (rotationMenu C)
    rcases normalized_saturation_progress P1 PG PR PF PU PI PO PN S D a b hD ha hb hconf
      M hM hML hLM menu with ht | hnext | ⟨B,hB,hmin,heq⟩
    · exact Or.inl ht
    · exact Or.inr (Or.inl hnext)
    · right
      right
      apply stable_package S D a b hD ha hb hconf M B hM hML hLM N hN hodd hgroup menu hB hmin heq C
      · intro f hf
        change (rotationMenu C).Processed f B
        exact BinaryMenu.Processed.right _ _ (hB.processed f hf)
      · intro hbad
        exact False.elim (hd (heq.symm.trans hbad))

end
end Paper2.SourceFaithful.HeightOne

