import Paper2.SourceFaithful.SourceStatements.TwoPointWalshPorts
import Paper2.SourceFaithful.SourceStatements.TwoPointWalshPair
import Paper2.SourceFaithful.SourceStatements.TwoPointWalshAnchor
import Paper2.Paper1ProvedGadgetProvider
import Paper2.Paper1ProvedOracleAdapters
import Paper2.SourceFaithful.GadgetAugmentation

/-! Literal constructive component of source Lemma 3.15: every even
complementary two-point Walsh signature of arity at least four, with a
root-of-unity coefficient ratio, produces an actual quaternary K anchor.
Port reindexing only changes their order, and the phase-correction binary is
derived from the same two-copy graph rather than supplied as an extra resource.
-/
namespace Paper2.SourceFaithful.SourceStatements.TwoPointWalsh
open Paper2.Tractable Paper2.ExactInput Paper2.HeightOne.PhaseCards
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Arbitrary even arity and arbitrary complementary support word. The
returned quaternary uses only the original realized h and native-X edges. -/
theorem even_root_anchor {F : SignatureFamily AlgebraicComplex} {n : ℕ}
    (hn : 4 ≤ n) (he : Even n) (h : Signature AlgebraicComplex n)
    (hh : NetworkRealizable F h)
    (a : Fin n → Bool) (c0 c1 : AlgebraicComplex) (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (hform : walshCoordinates h = twoPointForm a c0 c1)
    (ell : ℕ) (hell : 0 < ell) (hr : (c1/c0)^ell = 1) :
    ∃ (g : Signature AlgebraicComplex 4) (lam : AlgebraicComplex),
      NetworkRealizable F g ∧ lam ≠ 0 ∧
      Kernel.pullback Signature.disequality sourceKBasis.inverse = Signature.equality ∧
      sourceKBasis.action g = fun x => lam * equalityFour x := by
  obtain ⟨m,e,b,d0,d1,hm,hem,hb0,hb1,hd0,hd1,hr',hentry⟩ :=
    orient_even_twoPoint hn he a c0 c1 hc0 hc1 ell hr
  let h' := Tensor.reindex e h
  have hh' : NetworkRealizable F h' := hh.reindex e
  have hform' : walshCoordinates h' = twoPointForm b d0 d1 := by
    rw [walshCoordinates_reindex,hform,hentry]
  let q := TwoPointWalshPair.pair h'
  have hq : NetworkRealizable F q := TwoPointWalshPair.pair_realizable h' hh'
  have hw := TwoPointWalshPair.pair_walsh h' b d0 d1 hb0 hb1 (by omega) hem
    (by
      rw [hform']
      funext x
      simp [Paper2.SourceFaithful.SourceStatements.TwoPointWalsh.twoPointForm,
        point,TwoPointWalshPair.delta])
  let c := TwoPointWalshPair.tailScalar b * d0^2
  let r := (d1/d0)^2
  have hc : c ≠ 0 := mul_ne_zero (TwoPointWalshPair.tailScalar_ne_zero b)
    (pow_ne_zero _ hd0)
  have hqform : walshCoordinates q = endpoints c r := by
    rw [hw]
    funext x
    simp only [endpoints,c,r,TwoPointWalshPair.delta,point]
    field_simp
  have hrpow : r^ell = 1 := by
    dsimp [r]
    rw [← pow_mul,Nat.mul_comm 2 ell,pow_mul,hr']
    simp
  exact quaternary_root_anchor q hq c r hc hqform ell hell hrpow

/-- The graph above can be retained as a literal member in a finite language
equivalent to the original one. Both reductions are actual controlled
canonical-field reductions, instantiated with proved Paper 1 implementations.
-/
theorem root_anchor_enlargement (L : Language) {n : ℕ}
    (hn : 4 ≤ n) (he : Even n) (h : Signature AlgebraicComplex n)
    (hh : NetworkRealizable L.family h)
    (a : Fin n → Bool) (c0 c1 : AlgebraicComplex) (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (hform : walshCoordinates h = twoPointForm a c0 c1)
    (ell : ℕ) (hell : 0 < ell) (hr : (c1/c0)^ell = 1) :
    ∃ (M : Language) (g : Signature AlgebraicComplex 4) (lam : AlgebraicComplex),
      M.family = insert (⟨4,g⟩ : AnySignature AlgebraicComplex) L.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M ∧
      lam ≠ 0 ∧
      Kernel.pullback Signature.disequality sourceKBasis.inverse = Signature.equality ∧
      sourceKBasis.action g = fun x => lam * equalityFour x := by
  obtain ⟨g,lam,hg,hlam,hedge,hanchor⟩ :=
    even_root_anchor hn he h hh a c0 c1 hc0 hc1 hform ell hell hr
  obtain ⟨M,hM,hML,hLM⟩ := Paper1Proved.directGadgetProvider.adjoin_equivalence
    Paper1Proved.restrictionProvider L g (NativeNetworkRealizesUpTo.of_realizable hg)
  exact ⟨M,g,lam,hM,hML,hLM,hlam,hedge,hanchor⟩

end
end Paper2.SourceFaithful.SourceStatements.TwoPointWalsh

