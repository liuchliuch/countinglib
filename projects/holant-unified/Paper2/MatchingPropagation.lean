import Paper2.MatchingPropagation.Selection

/-!
# Paper 2, Lemma 8.4: propagation of literal X-matching products

Both alternatives of source `lem:hc-x-line-propagation` are proved. All port
sets, deleted occurrences, scalar coefficients, and two-term contractions are
actual data. Potentially zero contractions are proved nonzero by comparing
orders with a known X contraction. Factor rigidity is proved by coefficient
cancellation; no unique-factorization oracle or propagation field is assumed.

The proof establishes the stronger result for arbitrary nonsingular
anti-diagonal matching products. In particular it applies to the source's
ARS products, and does not need the separately stated EO/evenness assumptions.
-/
namespace Paper2.MatchingPropagation
open CommonPhase EndpointSelfLoop
variable {ι : Type}

theorem SamePair.trans {e f g : PortPair ι} (h : SamePair e f) (h' : SamePair f g) :
    SamePair e g := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases h' with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · exact Or.inl ⟨ha.trans hc,hb.trans hd⟩
  · exact Or.inr ⟨ha.trans hc,hb.trans hd⟩
  · exact Or.inr ⟨ha.trans hd,hb.trans hc⟩
  · exact Or.inl ⟨ha.trans hd,hb.trans hc⟩

/-- Source Lemma 8.4(2), in a stronger weighted form. `hm` says that the first
pair's ports lie on distinct edges of the matching after deleting `s`. -/
theorem propagation_condition_two [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hd : WeightedDeck F)
    (r s : PortPair ι) (hrs : r.Disjoint s) (hr : XAt F r)
    (Q : Matching (Remaining s.first s.second)) (c : ℂ) (hc : c ≠ 0)
    (hs : contraction F s = fun x => c * literal Q ℂ x)
    (hm : mate Q (s.residual r hrs.symm).first ≠ (s.residual r hrs.symm).second) :
    ∀ e, XAt F e := by
  have hsX : XAt F s := ⟨Q,c,hc,hs⟩
  have hW : ∀ e, e.Disjoint r → e.Disjoint s → XAt F e := by
    intro e her hes
    by_cases he : SamePair e (matePair s r hrs.symm Q)
    · obtain ⟨t,hrt,hst,het⟩ := exists_disjoint_three hn r s e
      have htn : ¬SamePair t (matePair s r hrs.symm Q) := by
        intro ht
        exact not_same_of_disjoint t e het.symm (ht.trans he.symm)
      have ht := nonexceptional_isX F hd r s hrs hr Q c hc hs hm t hrt.symm hst.symm htn
      exact isX_of_three_disjoint F hd e r s t her hes het hrs hrt hst hr hsX ht
    · exact nonexceptional_isX F hd r s hrs hr Q c hc hs hm e her hes he
  have haway := extend_from_common_complement hn F hd r s hr hW
  exact propagation_condition_one hn F hd r (fun e he => haway e he.symm)

/-- Source-exact ARS specialization of condition 2. -/
theorem propagation_condition_two_ARS [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hd : ARSDeck F)
    (r s : PortPair ι) (hrs : r.Disjoint s) (hr : XAt F r)
    (Q : Matching (Remaining s.first s.second)) (c : ℂ) (hc : c ≠ 0)
    (hs : contraction F s = fun x => c * literal Q ℂ x)
    (hm : mate Q (s.residual r hrs.symm).first ≠ (s.residual r hrs.symm).second) :
    ∀ e, XAt F e :=
  propagation_condition_two hn F hd.weighted r s hrs hr Q c hc hs hm

/-- The manuscript's second alternative, recording the actual witness matching
of the `ij` contraction and its two distinct incident matching edges. -/
def SecondCondition (F : Tensor ℂ ι) (r : PortPair ι) : Prop :=
  XAt F r ∧ ∃ (s : PortPair ι) (hrs : r.Disjoint s)
    (Q : Matching (Remaining s.first s.second)) (c : ℂ),
    c ≠ 0 ∧ contraction F s = (fun x => c * literal Q ℂ x) ∧
      mate Q (s.residual r hrs.symm).first ≠ (s.residual r hrs.symm).second

/-- Lemma 8.4, both alternatives, with zero contractions permitted in its deck
hypothesis. The conclusion explicitly requires a nonzero scalar at every pair. -/
theorem x_line_propagation [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hd : ARSDeck F) (r : PortPair ι)
    (h : (∀ e, r.Disjoint e → XAt F e) ∨ SecondCondition F r) :
    ∀ e, XAt F e := by
  rcases h with h | ⟨hr,s,hrs,Q,c,hc,hs,hm⟩
  · exact propagation_condition_one_ARS hn F hd r h
  · exact propagation_condition_two_ARS hn F hd r s hrs hr Q c hc hs hm

/-- Literal source wrapper: the EO and even-cardinality assumptions are
accepted explicitly, although the stronger algebraic proof does not need them. -/
theorem x_line_propagation_source [Fintype ι]
    (F : Tensor ℂ ι) (_heo : Tensor.ChargeLayer F 0)
    (_heven : Even (Fintype.card ι)) (hn : 8 ≤ Fintype.card ι)
    (hd : ARSDeck F) (r : PortPair ι)
    (h : (∀ e, r.Disjoint e → XAt F e) ∨ SecondCondition F r) :
    ∀ e : PortPair ι, ∃ (P : Matching (Remaining e.first e.second)) (c : ℂ),
      c ≠ 0 ∧ loop e.first e.second e.distinct F = fun x => c * literal P ℂ x :=
  x_line_propagation hn F hd r h

/-- The conclusion feeds the existing common-phase theorem as its full literal
matching deck, with the scalars selected from the proved existential witnesses. -/
theorem x_line_matching_deck [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hd : ARSDeck F) (r : PortPair ι)
    (h : (∀ e, r.Disjoint e → XAt F e) ∨ SecondCondition F r) :
    ∃ (lam : PortPair ι → ℂ)
      (P : (e : PortPair ι) → Matching (Remaining e.first e.second)),
      MatchingDeck F lam P ∧ ∀ e, lam e ≠ 0 := by
  classical
  have hx := x_line_propagation hn F hd r h
  choose P lam hnz he using hx
  exact ⟨lam,P,he,hnz⟩

/-- Exact compatibility with the existing finite-arity weighted-product class. -/
theorem isWeighted_iff_original {n : ℕ} (F : Signature ℂ n) :
    IsWeighted F ↔ WeightedMatching.IsProduct F := by
  constructor
  · rintro ⟨P,p,q,c,hc,hp,hq,hF⟩
    let Q : WeightedMatching.Pairing n := ⟨P.count,P.ports⟩
    refine ⟨Q,p,q,c,?_,hF⟩
    exact mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun j _ => mul_ne_zero (hp j) (hq j)))
  · rintro ⟨P,p,q,c,h,hF⟩
    obtain ⟨hc,hp,hq⟩ := WeightedMatching.parameters_nonzero P p q c h
    exact ⟨ofPairing P,p,q,c,hc,hp,hq,hF⟩

end Paper2.MatchingPropagation
