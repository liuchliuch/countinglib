import Paper2.RelativeEO.AmbientLifting
import Paper2.Paper1ProvedGadgetProvider
import Paper2.Paper1ProvedRestrictionProvider
import Paper2.SourceFaithful.SourceStatements.PublicReduction

/-! Source Lemma 3.6, closed over the actual direct-gadget and restriction
machines. The fixed-field programmes are transported through the executed
root codecs, uniformly over every correct bounded public target convention.
The finite derivation retains each ordered native-X graph and its nonzero
scalar. No proof-provider or ambient EO hypothesis is supplied by the caller.
-/
namespace Paper2.SourceFaithful.SourceStatements.RelativeEOAmbient
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
noncomputable section

/-- The actual fixed-gadget substitution machine, with strict public answers.
The augmented-to-original direction and all arbitrary target-answer bounds
are those of the executed codec transport. -/
theorem directGadget_strict : Paper2.Paper1DirectGadgetAccepted where
  directGadget_2_5 L M hLM h :=
    PublicReduction.of_fixed_field .nativeX M L
      (Paper2.Paper1Proved.directGadgetProvider.directGadget_2_5 L M hLM h)

/-- Literal finite label restriction with the same strict public convention. -/
theorem restriction_strict : Paper2.Paper1RestrictionAccepted where
  restriction_2_5 L M hLM :=
    PublicReduction.of_fixed_field .nativeX L M
      (Paper2.Paper1Proved.restrictionProvider.restriction_2_5 L M hLM)

/-- The same actual direct derivation is valid in the larger retained
language; the exact ambient union reduces to that original language; every
hard source subproblem of the derivation transfers to the ambient language.
Finiteness of the source set follows already from its inclusion in L.family.
-/
theorem source_3_6 (L : Language)
    {F : SignatureFamily AlgebraicComplex} (hFL : F ⊆ L.family)
    {S : List (AnySignature AlgebraicComplex)} (h : DirectDerivation F S) :
    DirectDerivation L.family S ∧
      (∃ M : Language, M.family = L.family ∪ generated S ∧
        Problem.Reduces .nativeX M L) ∧
      (∀ H : Language, H.family ⊆ F ∪ generated S →
        Problem.SharpPHard .nativeX H → Problem.SharpPHard .nativeX L) :=
  ⟨h.mono hFL, ambient_lifting directGadget_strict L hFL h,
    fun H hH hard =>
      ambient_hardness directGadget_strict restriction_strict L H hFL h hH hard⟩

/-- Any exact finite representation of the original ambient union has the
same strict reduction, without a caller restriction provider. -/
theorem source_3_6_to (L M : Language)
    {F : SignatureFamily AlgebraicComplex} (hFL : F ⊆ L.family)
    {S : List (AnySignature AlgebraicComplex)} (h : DirectDerivation F S)
    (hM : M.family = L.family ∪ generated S) : Problem.Reduces .nativeX M L :=
  ambient_lifting_to directGadget_strict restriction_strict L M hFL h hM

/-- The printed hardness clause for an actual source sublanguage. -/
theorem source_3_6_hardness (L H : Language)
    {F : SignatureFamily AlgebraicComplex} (hFL : F ⊆ L.family)
    {S : List (AnySignature AlgebraicComplex)} (h : DirectDerivation F S)
    (hH : H.family ⊆ F ∪ generated S) (hard : Problem.SharpPHard .nativeX H) :
    Problem.SharpPHard .nativeX L :=
  ambient_hardness directGadget_strict restriction_strict L H hFL h hH hard

end
end Paper2.SourceFaithful.SourceStatements.RelativeEOAmbient

