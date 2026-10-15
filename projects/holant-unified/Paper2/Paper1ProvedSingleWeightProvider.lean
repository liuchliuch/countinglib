import Paper2.SourceFaithful.SingleWeightPins
import Paper2.SourceFaithful.InitialBranches

/-! The negative single-weight theorem follows from the proved EO theorem and
the independent source gadget/factor reductions.  In the one-sided arm every
nonzero central restriction is an original literal row.  In the two-sided arm
the actual charged carriers supply both pins, so the complete EO dictionary
has actual networks over a retained oracle-equivalent augmentation. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SingleWeightProvider
open SourceFaithful.SingleWeight

private theorem completion_nonzero {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : f ≠ 0) (d : ℕ) : (Signature.completeToEO f d).2 ≠ 0 := by
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hf
  by_cases hc : n ≤ 2*d
  · rw [Signature.completeToEO,if_pos hc]
    intro hz
    have h := congrFun hz (Fin.append x (fun _ => false))
    exact hx (by simpa [Signature.completeWithZeros,Signature.tensor_apply,
      Signature.unaryPower,Signature.pointMass] using h)
  · rw [Signature.completeToEO,if_neg hc]
    intro hz
    have h := congrFun hz (Fin.append x (fun _ => true))
    exact hx (by simpa [Signature.completeWithOnes,Signature.tensor_apply,
      Signature.unaryPower,Signature.pointMass] using h)

private theorem completion_positive {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 0<n) (d : ℕ) : 0 < (Signature.completeToEO f d).1 := by
  unfold Signature.completeToEO
  split_ifs <;> dsimp <;> omega

private theorem central_subset (L : Language)
    (hlayers : ∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d) :
    centralFamily L.family ⊆ L.family := by
  rintro f ⟨g,hg,hne,rfl⟩
  obtain ⟨d,hd⟩ := hlayers g hg
  rw [hd.centralRestriction_eq_self (hd.arity_eq_twice_of_centralRestriction_ne_zero hne)]
  exact hg

private theorem central_isEO (L : Language)
    (hlayers : ∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d) :
    ∀ f ∈ centralFamily L.family, IsEO f := by
  rintro f ⟨g,hg,hne,rfl⟩
  obtain ⟨d,hd⟩ := hlayers g hg
  refine ⟨⟨d,hd.arity_eq_twice_of_centralRestriction_ne_zero hne⟩,?_⟩
  intro x hx
  exact if_neg hx

/-- The one-sided negative branch uses the literal original central rows.
The single-layer promise removes any global even-arity requirement. -/
theorem one_sided_hard (E : SourceFaithful.Paper1EOAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hlayers : ∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d)
    (hne : ¬ EOTract (centralFamily L.family)) : FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨H,hH⟩ := Language.coverage_family (centralFamily L.family)
    (Conformal.centralFamily_finite L.family_finite)
  have hsub : H.family ⊆ L.family := by
    rw [hH]
    exact central_subset L hlayers
  have hpH : Preprocessed H.family := fun f hf => hp f (hsub hf)
  have he : ∀ f ∈ H.family, IsEO f := by
    rw [hH]
    exact central_isEO L hlayers
  exact ((E.eo_2_16 H hpH he).2 (by simpa only [hH] using hne)).transport
    (R.restriction_2_5 H L hsub)

/-- The actual completed EO oracle reduces back to the original two-sided
single-layer language.  The completion is never supplied as a free gadget. -/
theorem two_sided_hard (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (Fac : SourceFaithful.Paper1FactorClosureAccepted)
    (E : SourceFaithful.Paper1EOAccepted) (R : SourceFaithful.Paper1RestrictionAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hlayers : ∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d)
    (hboth : BothChargeSigns L.family)
    (hne : ¬ EOTract (completionFamily L.family)) : FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨N,hLN,hzero,hone,_,hNL⟩ := both_pins G Fac L hp hlayers hboth
  obtain ⟨H,hH⟩ := Language.coverage_family (completionFamily L.family)
    (Conformal.completionFamily_finite L.family_finite)
  have hpH : Preprocessed H.family := by
    rw [hH]
    rintro f ⟨g,hg,hg0,d,_,rfl⟩
    exact ⟨completion_positive g.2 (hp g hg).1 d,completion_nonzero g.2 hg0 d⟩
  have he : ∀ f ∈ H.family, IsEO f := by
    rw [hH]
    rintro f ⟨g,_,_,d,hd,rfl⟩
    exact ⟨Signature.completeToEO_even g.2 d,Signature.completeToEO_central hd⟩
  have hreal : ∀ f ∈ H.family, NetworkRealizable N.family f.2 := by
    rw [hH]
    rintro f ⟨g,hg,_,d,_,rfl⟩
    exact completion_realizable N g.2 (hLN hg) hzero hone d
  obtain ⟨M,hM⟩ := Language.coverage_family (N.family ∪ H.family)
    (N.family_finite.union H.family_finite)
  have hNM : N.family ⊆ M.family := by rw [hM]; exact Set.subset_union_left
  have hHM : H.family ⊆ M.family := by rw [hM]; exact Set.subset_union_right
  have hMN : FixedFieldOutput.Reduces .nativeX M N := G.directGadget_2_5 N M hNM (by
    intro f hf
    rw [hM] at hf
    rcases hf with hf | hf
    · exact NativeNetworkRealizesUpTo.of_mem hf
    · exact NativeNetworkRealizesUpTo.of_realizable (hreal f hf))
  have hardH := (E.eo_2_16 H hpH he).2 (by simpa only [hH] using hne)
  exact hardH.transport ((R.restriction_2_5 H M hHM).trans (hMN.trans hNL))

end SingleWeightProvider

/-- Exact Theorem 2.17 negative conclusion, without an odd or unary theorem
parameter and without accepting any Paper 2 classification conclusion. -/
theorem singleWeightHard (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (Fac : SourceFaithful.Paper1FactorClosureAccepted)
    (E : SourceFaithful.Paper1EOAccepted) (R : SourceFaithful.Paper1RestrictionAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hlayers : ∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d)
    (hne : ¬ ((CommonOneSided L.family ∧ EOTract (centralFamily L.family)) ∨
      (BothChargeSigns L.family ∧ EOTract (completionFamily L.family)))) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  rcases commonOneSided_or_bothChargeSigns L.family with hs | hb
  · exact SingleWeightProvider.one_sided_hard E R L hp hlayers
      (fun ht => hne (Or.inl ⟨hs,ht⟩))
  · exact SingleWeightProvider.two_sided_hard G Fac E R L hp hlayers hb
      (fun ht => hne (Or.inr ⟨hb,ht⟩))

/-- A derived source theorem provider: only actual source gadget, factor,
EO and literal restriction implementations are needed to instantiate it. -/
def singleWeightProvider (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (Fac : SourceFaithful.Paper1FactorClosureAccepted)
    (E : SourceFaithful.Paper1EOAccepted) (R : SourceFaithful.Paper1RestrictionAccepted) :
    SourceFaithful.Paper1SingleWeightAccepted where
  singleWeight_2_17 := singleWeightHard G Fac E R

end
end Paper2.Paper1Proved
