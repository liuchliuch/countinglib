import Paper2.Synthesis.InitialBranches
import Paper2.ChargeBridgeReduction

/-! Section 9's retained, original-label reduction to the mountain interface.
The charge gcd is computed after prime-factor augmentation.  The result carries
the actual graph reductions, both endpoints, all-family charge divisibility,
and every original member; it is not a hardness oracle or a classification field. -/
namespace Paper2.Synthesis
open Paper2.Tractable Paper2.ExactInput Paper2.Problem

structure GcdMountainAugmentation (original : Language) where
  factorLanguage : Language
  decomposition : PrimeFactorization original
  factorFamily : factorLanguage.family = original.family ∪ decomposition.factors
  higherPrime : ∃ g ∈ factorLanguage.family, 2 < g.1 ∧ TensorPrime g.2
  language : Language
  height : ℕ
  isGcd : height = ChargeBridge.languageGcd factorLanguage
  mountain : Signature AlgebraicComplex (2 * height)
  isMountain : IsMountain mountain
  exactFamily : language.family = insert (⟨2 * height, mountain⟩ : AnySignature AlgebraicComplex)
    factorLanguage.family
  original_subset : original.family ⊆ language.family
  preprocessed : Preprocessed language.family
  even : ∀ g ∈ language.family, Even g.1
  divisible : ∀ g ∈ language.family, Tensor.HalfChargeDivisible g.2 height
  forward : Reduces .nativeX language original
  backward : Reduces .nativeX original language

theorem GcdMountainAugmentation.nontractable {L : Language} (A : GcdMountainAugmentation L)
    (h : ¬ Tract (kImage L)) : ¬ Tract (kImage A.language) :=
  fun ht => h (ht.mono_family (familyAction_mono sourceKBasis A.original_subset))

theorem GcdMountainAugmentation.member {L : Language} (A : GcdMountainAugmentation L) :
    (⟨2 * A.height, A.mountain⟩ : AnySignature AlgebraicComplex) ∈ A.language.family := by
  rw [A.exactFamily]
  exact Or.inl rfl

theorem mountain_halfCharge_divisible {d : ℕ} {f : Signature AlgebraicComplex (2 * d)}
    (hf : IsMountain f) : Tensor.HalfChargeDivisible f d := by
  intro x hx
  rcases hf.support_layers x hx with h | h | h
  · subst x
    rw [halfCharge_false]
    exact ⟨-1, by ring⟩
  · rw [h]
    exact dvd_zero _
  · subst x
    rw [halfCharge_true]

/-- Literal unary/binary prime factors give exactly source alternative (3),
with their ordered port partition and scalar retained under the K action. -/
theorem tract_of_low_factors (L : Language) (D : PrimeFactorization L)
    (hsmall : ∀ i j, (D.decomposition i).arity j ≤ 2) : Tract (kImage L) := by
  have ha : ArityTwoAlternative L.family := by
    rintro g ⟨i, rfl⟩
    right
    refine ⟨D.decomposition i, ?_, D.exact_value i⟩
    intro j
    have hp := D.positive i j
    have hs := hsmall i j
    omega
  have hk : ArityTwoAlternative (kImage L) := Conformal.arityTwo_map sourceKBasis ha
  exact ⟨(L.family_finite.image _).subset (fun _ h => h.1),
    Or.inr (Or.inr (Or.inl (hk.mono_family (fun _ h => h.1))))⟩

theorem signs_as_halfCharges (L : Language) (heven : ∀ g ∈ L.family, Even g.1)
    (htwo : ¬ CommonOneSided L.family) :
    (∃ i, ∃ x : Fin (L.arity i.val) → Bool, L.signature i x ≠ 0 ∧ 0 < halfCharge x) ∧
    (∃ i, ∃ x : Fin (L.arity i.val) → Bool, L.signature i x ≠ 0 ∧ halfCharge x < 0) := by
  have hboth : BothChargeSigns L.family :=
    (commonOneSided_or_bothChargeSigns L.family).resolve_left htwo
  have hd : ∀ (i : Fin L.count) (x : Fin (L.arity i.val) → Bool),
      charge x = 2 * halfCharge x := by
    intro i x
    simpa only [charge, doubledCharge, Fintype.card_fin] using
      (twice_halfCharge (by simpa using heven _ ⟨i, rfl⟩) x).symm
  constructor
  · obtain ⟨g, ⟨i, rfl⟩, x, hx, hc⟩ := hboth.2
    exact ⟨i, x, hx, by rw [hd] at hc; omega⟩
  · obtain ⟨g, ⟨i, rfl⟩, x, hx, hc⟩ := hboth.1
    exact ⟨i, x, hx, by rw [hd] at hc; omega⟩

/-- The finite augmentation records the source's gcd after factor closure, and
the explicit unary outcome is completely discharged by the accepted unary exit. -/
theorem gcd_mountain_or_hard
    (PO : Paper1OddAccepted) (PD : Paper1DirectGadgetAccepted)
    (PF : Paper1FactorClosureAccepted) (PR : Paper1RestrictionAccepted)
    (PU : Paper1UnaryAccepted) (L : Language) (hpre : Preprocessed L.family)
    (htwo : ¬ CommonOneSided L.family) (hnot : ¬ Tract (kImage L)) :
    Nonempty (GcdMountainAugmentation L) ∨ SharpPHard .nativeX L := by
  classical
  obtain ⟨D, B, hB, hBL, hLB⟩ := factorClosure_exists PF L hpre htwo
  have hsub : L.family ⊆ B.family := by rw [hB]; exact Set.subset_union_left
  have hpreB : Preprocessed B.family := by rw [hB]; exact D.retained_preprocessed hpre
  have hnotB : ¬ Tract (kImage B) :=
    fun h => hnot (h.mono_family (familyAction_mono sourceKBasis hsub))
  have hlarge : ∃ g ∈ B.family, 2 < g.1 ∧ TensorPrime g.2 := by
    by_contra hnone
    apply hnot
    apply tract_of_low_factors L D
    intro i j
    by_contra hsize
    apply hnone
    refine ⟨⟨(D.decomposition i).arity j, (D.decomposition i).factor j⟩, ?_, by change 2 < (D.decomposition i).arity j; omega, D.prime i j⟩
    rw [hB]
    exact Or.inr ⟨⟨i, j⟩, rfl⟩
  by_cases hodd : ∃ g ∈ B.family, Odd g.1 ∧ g.2 ≠ 0
  · right
    rcases odd_classification_preprocessed PO B hpreB hodd with ht | hh
    · exact False.elim (hnotB ht)
    · exact hh.transport_equivalence hBL hLB
  have heven : ∀ g ∈ B.family, Even g.1 := by
    intro g hg
    rcases Nat.even_or_odd g.1 with he | ho
    · exact he
    · exact False.elim (hodd ⟨g, hg, ho, (hpreB g hg).2⟩)
  have htwoB : ¬ CommonOneSided B.family := fun h => htwo (h.mono_family hsub)
  obtain ⟨hpos, hneg⟩ := signs_as_halfCharges B heven htwoB
  obtain ⟨hd, hdiv, hm | hh⟩ := ChargeBridge.nontractable_charge_bridge
    PD PF PR PU B hpreB (fun i => heven _ ⟨i, rfl⟩) hpos hneg hnotB
  · obtain ⟨f, hf, M, hM, hMB, hBM⟩ := hm
    left
    refine ⟨{
      factorLanguage := B
      decomposition := D
      factorFamily := hB
      higherPrime := hlarge
      language := M
      height := ChargeBridge.languageGcd B
      isGcd := rfl
      mountain := f
      isMountain := hf
      exactFamily := hM
      original_subset := ?_
      preprocessed := ?_
      even := ?_
      divisible := ?_
      forward := hMB.trans hBL
      backward := hLB.trans hBM }⟩
    · rw [hM]
      exact hsub.trans (Set.subset_insert _ _)
    · rw [hM]
      exact ChargeBridge.preprocessed_insert hpreB (by omega)
        (fun h => hf.zero_ne_zero (congrFun h _))
    · rw [hM]
      intro g hg
      rcases hg with rfl | hg
      · exact even_two_mul _
      · exact heven g hg
    · rw [hM]
      intro g hg
      rcases hg with rfl | ⟨i, rfl⟩
      · exact mountain_halfCharge_divisible hf
      · exact hdiv i
  · exact Or.inr (hh.transport_equivalence hBL hLB)

end Paper2.Synthesis

