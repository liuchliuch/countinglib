import Paper2.SourceFaithful.LocalInputs

/-! Source-convention adapters for literal retained gadget augmentations.
Pure graph realizability is reused unchanged; only the answer convention of
actual controlled reductions is the new canonical fixed-field one. -/
namespace Paper2.SourceFaithful
open Tractable ExactInput
namespace Paper1DirectGadgetAccepted

 theorem adjoin_equivalence (P : Paper1DirectGadgetAccepted)
    (R : Paper1RestrictionAccepted) (L : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : NativeNetworkRealizesUpTo L.family f) :
    ∃ M : Language, M.family = insert (⟨n,f⟩ : AnySignature AlgebraicComplex) L.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨M,hM,hML⟩ := P.adjoin L f hf
  refine ⟨M,hM,hML,R.restriction_2_5 L M ?_⟩
  rw [hM]
  exact Set.subset_insert _ _

 theorem adjoin_pair (P : Paper1DirectGadgetAccepted) (L : Language) {m n : ℕ}
    (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
    (hf : NativeNetworkRealizesUpTo L.family f)
    (hg : NativeNetworkRealizesUpTo L.family g) :
    ∃ M : Language,
      M.family = insert (⟨m,f⟩ : AnySignature AlgebraicComplex)
        (insert (⟨n,g⟩ : AnySignature AlgebraicComplex) L.family) ∧
      FixedFieldOutput.Reduces .nativeX M L := by
  obtain ⟨M,hM⟩ := Language.coverage_family _
    ((L.family_finite.insert ⟨n,g⟩).insert ⟨m,f⟩)
  refine ⟨M,hM,P.directGadget_2_5 L M ?_ ?_⟩
  · intro k hk; rw [hM]; exact Or.inr (Or.inr hk)
  · intro k hk
    rw [hM] at hk
    rcases hk with rfl | rfl | hk
    · exact hf
    · exact hg
    · exact NativeNetworkRealizesUpTo.of_mem hk
end Paper1DirectGadgetAccepted
end Paper2.SourceFaithful
