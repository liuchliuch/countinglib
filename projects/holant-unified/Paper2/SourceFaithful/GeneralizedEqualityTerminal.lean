import Paper2.SourceFaithful.RelativeEO.Terminal
import Paper2.RelativeEO.GeneralizedEqualityGadget

/-! The endpoint-only branch has an actual Paper 2 terminal.  Two copies of
the supplied generalized equality and n−2 literal X edges produce the exact
nonzero complementary EO quaternary.  Its two-point support excludes B_ARS,
so the independently proved relative EO terminal closes the original ambient
problem.  No external generalized-equality terminal is postulated. -/
namespace Paper2.SourceFaithful
open Tractable ExactInput Paper2.RelativeEO EndpointSelfLoop

/-- A generalized equality of any arity at least three, genuinely realizable
over the source language, is a relative whole-language terminal. -/
theorem generalized_equality_relative_terminal
    (G : Paper1DirectGadgetAccepted) (O : Paper1OccurrenceAccepted)
    (Fac : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {q : ℕ} (hq : 3 ≤ q)
    (f : Signature AlgebraicComplex q) (a b : AlgebraicComplex) (hab : a*b ≠ 0)
    (hform : ∀ x, f x = (if x = (fun _ => false) then a else 0) +
      (if x = (fun _ => true) then b else 0))
    (hgraph : NetworkRealizable L.family f) : FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  let i : Fin q := ⟨0,by omega⟩
  let j : Fin q := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have hh := congrArg Fin.val h; simp [i,j] at hh
  have hne : (fun _ : Fin q => false) ≠ (fun _ => true) := by
    intro h
    exact Bool.false_ne_true (congrFun h i)
  have hf : f ≠ 0 := by
    intro hz
    have hh := hform (fun _ => false)
    rw [hz] at hh
    have ha : a = 0 := by simpa [hne] using hh.symm
    exact hab (by rw [ha,zero_mul])
  obtain ⟨N,hN,_,hpreN,hbothN,hnotN,hNL⟩ := RelativeEO.retained_output G
    L hpre hboth hnot f (by omega) hf (NativeNetworkRealizesUpTo.of_realizable hgraph)
  have hmem : (⟨q,f⟩ : AnySignature AlgebraicComplex) ∈ N.family := by
    rw [hN]
    exact Set.mem_insert _ _
  have hfGE : f = generalizedEquality a b := funext hform
  have hquad : gramTable i j hij f = fun x => (a*b) * complementaryE x := by
    rw [hfGE]
    exact generalizedEquality_gram_formula hq i j hij a b
  have hquadne : gramTable i j hij f ≠ 0 := by
    rw [hquad]
    exact scaledComplementary_ne_zero (a*b) hab
  have hquadEO : Signature.CentralSupport (gramTable i j hij f) := by
    rw [hquad]
    exact scaledComplementary_central (a*b)
  have hquadout : ¬ IsARSProduct (gramTable i j hij f) := by
    intro hh
    have hm := hh.isProduct
    rw [hquad] at hm
    exact scaledComplementary_not_matching (a*b) hab hm
  exact (RelativeEO.realized_relative_terminal G O Fac U E R B N hpreN hbothN hnotN
    (gramTable i j hij f) (by decide) hquadne hquadEO
    (gramTable_realized i j hij f hmem) hquadout).transport hNL

end Paper2.SourceFaithful
