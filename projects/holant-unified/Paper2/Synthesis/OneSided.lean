import Paper2.Synthesis.CentralConservation
import Paper2.Synthesis.SameGraphHardness
import Paper2.ExactInput.UnconditionalTransport
import Paper2.Paper1Accepted.Terminals
import Paper2.Tractable.Conformal.CommonBasis
import Paper2.Tractable.Downward

/-! Section 9's common-one-sided branch, before factor extraction.  Charge
conservation is applied to the literal original network, not to an unimplemented
graph simplification.  The weighted-EO theorem is used only on an all-EO family. -/
namespace Paper2.Synthesis
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation Paper2.Problem

noncomputable def centralLanguage (L : Language) : Language :=
  indexedLanguage L (fun _ f => Signature.centralRestriction f)

@[simp] theorem centralLanguage_count (L : Language) :
    (centralLanguage L).count = L.count := indexedLanguage_count L _

@[simp] theorem centralLanguage_arity (L : Language) :
    (centralLanguage L).arity = L.arity := indexedLanguage_arity L _

@[simp] theorem centralLanguage_family (L : Language) :
    (centralLanguage L).family =
      (fun g : AnySignature AlgebraicComplex => ⟨g.1, Signature.centralRestriction g.2⟩) '' L.family :=
  indexedLanguage_family L _

noncomputable def centralInstanceEquiv (L : Language) :
    Instance L ≃ Instance (centralLanguage L) :=
  reinterpretEquiv (centralLanguage_count L).symm (centralLanguage_arity L).symm

@[simp] theorem centralInstance_bytes (L : Language) (G : Instance L) :
    (inputEncoding (centralLanguage L)).encode (centralInstanceEquiv L G) =
      (inputEncoding L).encode G := rfl

private theorem reinterpret_central_value {s t : ℕ} {a b : ℕ → ℕ}
    (hs : s = t) (ha : a = b)
    (G : {r : Complexity.RawClosedNetwork // r.WellFormed s 1 a})
    (f : (i : Fin s) → Signature AlgebraicComplex (a i.val))
    (g : (i : Fin t) → Signature AlgebraicComplex (b i.val))
    (hvertex : ∀ i, HEq (g (Fin.cast hs i)) (Signature.centralRestriction (f i)))
    (hside : (∀ i x, f i x ≠ 0 → 0 ≤ doubledCharge x) ∨
      (∀ i x, f i x ≠ 0 → doubledCharge x ≤ 0)) :
    ((reinterpret hs ha G).val.realize (reinterpret hs ha G).property g
      (fun _ => Signature.disequality)).denote Fin.elim0 =
    (G.val.realize G.property f (fun _ => Signature.disequality)).denote Fin.elim0 := by
  cases hs
  cases ha
  have hg : g = fun i => Signature.centralRestriction (f i) :=
    funext (fun i => eq_of_heq (hvertex i))
  subst g
  apply Network.centralize_denote (G.val.realize G.property f (fun _ => Signature.disequality))
    (fun _ => rfl)
  rcases hside with h | h
  · exact Or.inl (fun v x hx => h (G.val.signatureLabel G.property v) x hx)
  · exact Or.inr (fun v x hx => h (G.val.signatureLabel G.property v) x hx)

/-- Every original graph, including loops and disconnected scalar components,
has exactly the same value after central restriction of all its indexed tables. -/
theorem centralInstance_value (L : Language) (hside : CommonOneSided L.family) (G : Instance L) :
    value .nativeX (centralLanguage L) (centralInstanceEquiv L G) = value .nativeX L G := by
  apply reinterpret_central_value (centralLanguage_count L).symm (centralLanguage_arity L).symm G
    L.signature (centralLanguage L).signature
    (fun i => indexedLanguage_signature L (fun _ f => Signature.centralRestriction f) i)
  rcases hside with h | h
  · left
    intro i x hx
    simpa only [charge, doubledCharge, Fintype.card_fin] using h _ ⟨i, rfl⟩ x hx
  · right
    intro i x hx
    simpa only [charge, doubledCharge, Fintype.card_fin] using h _ ⟨i, rfl⟩ x hx

theorem centralFamily_subset_centralLanguage (L : Language) :
    centralFamily L.family ⊆ (centralLanguage L).family := by
  rintro h ⟨g, hg, _, rfl⟩
  rw [centralLanguage_family]
  exact ⟨g, hg, rfl⟩

theorem centralLanguage_allEO (L : Language) (heven : ∀ g ∈ L.family, Even g.1) :
    ∀ g ∈ (centralLanguage L).family, IsEO g := by
  rw [centralLanguage_family]
  rintro g ⟨h, hh, rfl⟩
  obtain ⟨d, hd⟩ := heven h hh
  refine ⟨⟨d, by change h.1 = 2 * d; omega⟩, ?_⟩
  intro x hx
  exact if_neg hx

/-- Source clause (1) with the single family-wide support orientation intact. -/
theorem tract_of_one_sided (L : Language) (hpre : Preprocessed L.family)
    (hside : CommonOneSided L.family) (heo : EOTract (centralFamily L.family)) :
    Tract (kImage L) := by
  have hp : Preprocessed (kImage L) := Conformal.preprocessed_familyAction _ hpre
  rw [Tract, preprocess_eq_self hp]
  refine ⟨L.family_finite.image _, Or.inl ?_⟩
  simpa only [OneSidedAlternative, kImage, Conformal.kCoordinates_familyAction] using And.intro hside heo

/-- Actual encoded hardness follows from all-EO hardness with the very same
oracle program and graph bytes.  No ambient relative-EO assumption is used. -/
theorem one_sided_classification (PE : Paper1EOAccepted) (PR : Paper1RestrictionAccepted)
    (L : Language)
    (hpre : Preprocessed L.family) (heven : ∀ g ∈ L.family, Even g.1)
    (hside : CommonOneSided L.family) :
    Tract (kImage L) ∨ SharpPHard .nativeX L := by
  classical
  by_cases heo : EOTract (centralFamily L.family)
  · exact Or.inl (tract_of_one_sided L hpre hside heo)
  · obtain ⟨H, hH⟩ := Language.coverage_family (centralFamily L.family)
      ((centralLanguage L).family_finite.subset (centralFamily_subset_centralLanguage L))
    have hsub : H.family ⊆ (centralLanguage L).family := by
      rw [hH]
      exact centralFamily_subset_centralLanguage L
    have hpH : Preprocessed H.family := by
      rw [hH]
      rintro g ⟨f, hf, hnz, rfl⟩
      exact ⟨(hpre f hf).1, hnz⟩
    have hardH := (PE.eo_2_16 H hpH (fun g hg => centralLanguage_allEO L heven g (hsub hg))).2
      (by simpa only [hH] using heo)
    have hard := hardH.transport_unconditional (PR.restriction_2_5 H (centralLanguage L) hsub)
    right
    apply hard.sameGraph (centralInstanceEquiv L).symm
    · intro G
      exact (centralInstance_bytes L ((centralInstanceEquiv L).symm G)).symm.trans
        (congrArg _ ((centralInstanceEquiv L).apply_symm_apply G))
    · intro G
      exact (centralInstance_value L hside ((centralInstanceEquiv L).symm G)).symm.trans
        (congrArg _ ((centralInstanceEquiv L).apply_symm_apply G))

end Paper2.Synthesis

