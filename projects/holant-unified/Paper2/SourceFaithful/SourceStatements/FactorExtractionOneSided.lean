import Paper2.Paper1ProvedOddProvider
import Paper2.HeightTwo.OriginalLanguage
import Paper2.SourceFaithful.PublicHardness
import Paper2.TractableAlgorithms.PublicEvaluation

/-! The common-one-sided exception of source Theorem 2.14 on the actual
original finite language. Zero and nullary rows are retained in evaluation.
The same sign and A/P class witness survives their structural preprocessing;
the negative branch is transported back by the actual restriction machine.
No caller preprocessing, all-even or proof-provider premise is needed.
-/
namespace Paper2.SourceFaithful.SourceStatements.FactorExtraction
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.Synthesis
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Central restriction commutes with removing precisely zero and nullary
original rows. A nonzero restriction already proves its original row nonzero.
-/
theorem centralFamily_preprocess (F : SignatureFamily AlgebraicComplex) :
    centralFamily (preprocess F) = preprocess (centralFamily F) := by
  ext g
  constructor
  · rintro ⟨f, ⟨hf, hn, _⟩, hc, rfl⟩
    exact ⟨⟨f, hf, hc, rfl⟩, hn, hc⟩
  · rintro ⟨⟨f, hf, hc, rfl⟩, hn, _⟩
    refine ⟨f, ⟨hf, hn, ?_⟩, hc, rfl⟩
    intro hz
    apply hc
    rw [hz]
    funext x
    simp [Signature.centralRestriction]

/-- Adding zero and nullary EO rows keeps the original single family-wide
sign and A/P class. All nullary restrictions are actual constant signatures.
The EO domain requirement remains explicit for this general structural fact.
-/
theorem eoTract_preprocess_iff (F : SignatureFamily AlgebraicComplex)
    (hF : F.Finite) (hEO : ∀ g ∈ F, IsEO g) :
    EOTract (preprocess F) ↔ EOTract F := by
  constructor
  · rintro ⟨_, _, sign, C, hx, hp⟩
    refine ⟨hF, hEO, sign, C, ?_, ?_⟩
    · rintro ⟨n, f⟩ hf a b c ha hb hc
      by_cases hz : f = 0
      · exact False.elim (ha (by rw [hz]; rfl))
      cases n with
      | zero =>
        have he : tripleXor a b c = a := Subsingleton.elim _ _
        left
        simpa only [he] using ha
      | succ n => exact hx ⟨n + 1, f⟩ ⟨hf, Nat.zero_lt_succ n, hz⟩ a b c ha hb hc
    · rintro ⟨n, f⟩ hf p
      by_cases hz : f = 0
      · subst f
        cases C with
        | affine =>
          change Affine (0 : Signature AlgebraicComplex p.count)
          exact affine_zero p.count
        | product =>
          change Product (0 : Signature AlgebraicComplex p.count)
          exact product_zero p.count
      cases n with
      | zero =>
        have he : p.restrict f = fun _ => f (fun j => Fin.elim0 j) := by
          funext x
          exact congrArg f (Subsingleton.elim _ _)
        rw [he]
        cases C with
        | affine => exact affine_constant p.count _
        | product => exact product_constant p.count _
      | succ n => exact hp ⟨n + 1, f⟩ ⟨hf, Nat.zero_lt_succ n, hz⟩ p
  · intro h
    exact h.mono_family (fun _ hg => hg.1)

/-- Exact restoration of the original central EO criterion, including all
original nullary coefficients and odd rows whose central restrictions vanish.
-/
theorem centralEO_preprocess_iff (L : Language) :
    EOTract (centralFamily (preprocess L.family)) ↔ EOTract (centralFamily L.family) := by
  rw [centralFamily_preprocess]
  exact eoTract_preprocess_iff _ (Conformal.centralFamily_finite L.family_finite)
    (Paper2.Paper1Proved.OddProvider.centralFamily_allEO L.family)

/-- The two exact printed complexity branches of the source factor-extraction
exception, on any common-one-sided original finite language. -/
theorem common_side_exception (L : Language) (hs : CommonOneSided L.family) :
    (EOTract (centralFamily L.family) → Problem.InFP .nativeX L) ∧
      (¬ EOTract (centralFamily L.family) → Problem.SharpPHard .nativeX L) := by
  obtain ⟨N, hN⟩ := Language.coverage_family (preprocess L.family)
    (L.family_finite.subset (fun _ h => h.1))
  have hp : Preprocessed N.family := by
    rw [hN]
    exact preprocess_preprocessed _
  have hNL : N.family ⊆ L.family := by
    rw [hN]
    exact fun _ h => h.1
  have hsN : CommonOneSided N.family := hs.mono_family hNL
  have hcentral : EOTract (centralFamily N.family) ↔ EOTract (centralFamily L.family) := by
    rw [hN]
    exact centralEO_preprocess_iff L
  constructor
  · intro he
    have htN := tract_of_one_sided N hp hsN (hcentral.mpr he)
    have htL := (Paper2.HeightTwo.kImage_preprocessed_tract_iff L N hN).mp htN
    exact Paper2.TractableAlgorithms.native_public_inFP_of_tract L htL
  · intro hn
    have hnN : ¬ EOTract (centralFamily N.family) := fun he => hn (hcentral.mp he)
    have hardN := Paper2.Paper1Proved.OddProvider.oneSided_failure_hard
      Paper2.Paper1Proved.eoProvider Paper2.Paper1Proved.restrictionProvider N hp hsN hnN
    have hardL := hardN.transport
      (Paper2.Paper1Proved.restrictionProvider.restriction_2_5 N L hNL)
    exact Paper2.SourceFaithful.public_hardness_of_fixed_field .nativeX L hardL

end
end Paper2.SourceFaithful.SourceStatements.FactorExtraction

