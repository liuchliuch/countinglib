import Counting.MatchgateWidth.PaperProofs

/-!
# Public matchgate-width flagship contracts

These aliases retain the explicit upstream contracts and their definitions.
The trichotomy is for full-rank, port-deficient, bi-essential qutrit common
presentations in the ordered planar model. It is a support-geometry theorem.
The lower bounds quantify over equivalent presentations with arbitrary finite
nonempty domains and complex weights, retaining labels, arities and port order.
-/
namespace Counting.MatchgateWidth

/-- Paper 3.1: one common rational qutrit family, its flag structure, attained
minimum exact width, explicit lower bounds and asymptotic growth. -/
theorem integer_unbounded_width : _root_.MatchgateWidth.Paper.claim_3_1 :=
  _root_.MatchgateWidth.Paper.claim_3_1_verified

/-- Paper 3.2: no universal domain-only bound, even for rational graph
presentations satisfying the displayed positivity and deficiency hypotheses. -/
theorem no_domain_only_width_bound : _root_.MatchgateWidth.Paper.claim_3_2 :=
  _root_.MatchgateWidth.Paper.claim_3_2_verified

/-- Paper 3.3: exhaustive and pairwise-exclusive ray, mobile and flag branches,
under all of the original common-presentation and support assumptions. -/
theorem qutrit_support_trichotomy : _root_.MatchgateWidth.Paper.claim_3_3 :=
  _root_.MatchgateWidth.Paper.claim_3_3_verified

/-- The separate unbounded-family clause; the flag branch alone is not a
characterization of minimum width. -/
theorem flag_family_unbounded : _root_.MatchgateWidth.Paper.claim_3_3_family :=
  _root_.MatchgateWidth.Paper.claim_3_3_family_verified

/-- Paper 4.2: exact ordered graph realization over the specified subfield. -/
theorem field_preserving_realization : _root_.MatchgateWidth.Paper.claim_4_2 :=
  _root_.MatchgateWidth.Paper.claim_4_2_verified

/-- Paper 9.1: transcendental companion with its own instance-class minimum. -/
theorem transcendental_companion : _root_.MatchgateWidth.Paper.claim_9_1 :=
  _root_.MatchgateWidth.Paper.claim_9_1_verified

/-- Paper 10.5: exact cover compression with labels and tensor order retained. -/
theorem labelwise_cover_compression : _root_.MatchgateWidth.Paper.claim_10_5 :=
  _root_.MatchgateWidth.Paper.claim_10_5_verified

/-- Paper 10.7: connection-prime collapse, including the two-plane refinement. -/
theorem connection_prime_collapse : _root_.MatchgateWidth.Paper.claim_10_7 :=
  _root_.MatchgateWidth.Paper.claim_10_7_verified

/-- Paper 10.10: the fixed-basis binary-context alternative. -/
theorem binary_context_alternative : _root_.MatchgateWidth.Paper.claim_10_10 :=
  _root_.MatchgateWidth.Paper.claim_10_10_verified

end Counting.MatchgateWidth
