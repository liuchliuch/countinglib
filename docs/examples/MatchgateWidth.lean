import Counting.Flagships.MatchgateWidth

/-!
# An exact-width obstruction on a concrete rational qutrit family

We choose the actual ordered-planar instance class and the integer family's
`k = 16` presentation. The public flagship theorem implies that no exact
width-two presentation can reproduce this language on that class, even after
changing to an arbitrary finite nonempty domain or relabelling the shape.
These are exact representation and support statements, not bit-time bounds
for evaluating partition functions. Ordered ports and the instance class stay
fixed throughout.
-/

namespace Counting.Tutorial.MatchgateWidth

noncomputable section

open _root_.MatchgateWidth

/-- The chosen class consists precisely of instances with a certificate for
the source's ordered planar drawing model; it is independent of tensor values. -/
def orderedPlanarInstances (k : ℕ) : LabelledInstanceClass (starLanguageShape (k + 2)) :=
  fun _ _ _ I => Nonempty I.OrderedPlanar

theorem orderedPlanar_contains (k : ℕ) : ContainsOrderedPlanar (orderedPlanarInstances k) :=
  fun _ _ _ _ h => h

/-- An actual common presentation on the three-element domain, at displayed
width `2^16 + 3`; this displayed width is not asserted to be minimal. -/
def sample : LabelledCommonPresentation (starLanguageShape 18) (Fin 3) (2 ^ 16 + 3) :=
  integerRationalPresentation 16 (by decide)

theorem sample_language : sample.language = integerControlledLanguage 16 (by decide) :=
  integerRationalPresentation_language 16 (by decide)

theorem sample_rank_three : sample.baseMatrix.rank = 3 :=
  controlledLabelledBase_rank 16

/-- The finite graph presentation uses rational weights. -/
theorem sample_rational_graphs : RationalGraphPresentation sample :=
  integerRationalPresentation_rational_graphs 16 (by decide)

/-- The induced language is integer-valued, has positive arities, and every
primitive port flattening is deficient relative to the qutrit domain. -/
theorem sample_positive_deficient : IntegerPositiveDeficient sample.language := by
  rw [sample_language]
  exact integerControlledLanguage_qualifies 16 (by decide)

/-- Instantiate the public unbounded-family result at `B = 2`, so that
`4 * B + 8 = 16`. The minimum ranges over all finite competitor domains. -/
theorem sample_minimum_exceeds_two : 2 < integerSourceMinimum orderedPlanarInstances 16 := by
  exact (Counting.MatchgateWidth.flag_family_unbounded
    orderedPlanarInstances orderedPlanar_contains).2.2 2

theorem sample_has_no_width_two :
    ¬ HasExactCommonWidthOn (orderedPlanarInstances 16) sample.language 2 := by
  intro h
  rw [sample_language] at h
  have hmin := integerSourceMinimum_le orderedPlanarInstances 16 (by decide) h
  exact (Nat.not_le_of_gt sample_minimum_exceeds_two) hmin

/-- In particular, supplying a new domain and a valid width-two presentation
cannot give exact labelled equivalence on the chosen ordered-planar class. -/
theorem no_width_two_replacement {E : Type} [Fintype E] [Nonempty E]
    {T : LabelledShape} (q : LabelledCommonPresentation T E 2) :
    ¬ ExactlyLabelledEquivalentOn (orderedPlanarInstances 16) sample.language q.language := by
  intro h
  exact sample_has_no_width_two ⟨E, inferInstance, inferInstance, T, q, h⟩

/-- The same concrete language is available in the public partition model,
with every label, edge identity, and port occurrence retained. -/
theorem sample_public_partition {a b c : ℕ}
    (I : LabelledInstance (starLanguageShape 18) a b c) :
    (Counting.MatchgateWidth.Semantics.closedInstance I sample.language).partition Empty.elim =
      I.value sample.language :=
  Counting.MatchgateWidth.Semantics.closedInstance_partition I sample.language Empty.elim

end

end Counting.Tutorial.MatchgateWidth
