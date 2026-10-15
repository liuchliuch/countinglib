import Paper2.RelativeEO.DiagonalPullback
import Paper2.RelativeEO.ARSMatching
import Paper2.HighHeightNormalization.FiniteAttachments

/-! Exact algebraic inverse-normalization bridge. Every new matching weight
is algebraic; a complex IsX reconstruction is descended using an actual input
coefficient before undoing the finite attachment sequence. -/
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput
open scoped BigOperators
open MatchingPropagation CommonPhase

/-- The two ordered matching APIs have exactly the same nonzero class. -/
theorem isWeighted_iff_isProduct {K : Type*} [Field K] {n : ℕ} (f : Signature K n) :
    IsWeighted f ↔ WeightedMatching.IsProduct f := by
  constructor
  · rintro ⟨P,p,q,c,hc,hp,hq,hf⟩
    exact ⟨⟨P.count,P.ports⟩,p,q,c,mul_ne_zero hc
      (Finset.prod_ne_zero_iff.mpr (fun j _ => mul_ne_zero (hp j) (hq j))),hf⟩
  · rintro ⟨P,p,q,c,hn,hf⟩
    obtain ⟨hc,hp,hq⟩ := WeightedMatching.parameters_nonzero P p q c hn
    exact ⟨ofPairing P,p,q,c,hc,hp,hq,hf⟩

noncomputable def algebraicMatingWeight (z : AlgebraicComplex) (b : Bool) : AlgebraicComplex :=
  if b then z else conjugateAlgebraic z

@[simp] theorem coe_algebraicMatingWeight (z : AlgebraicComplex) (b : Bool) :
    (algebraicMatingWeight z b : ℂ) = HighHeightNormalization.matingWeight (z : ℂ) b := by
  cases b <;> rfl

theorem algebraicMatingWeight_ne_zero {z : AlgebraicComplex} (hz : z ≠ 0) (b : Bool) :
    algebraicMatingWeight z b ≠ 0 := by
  cases b
  · exact conjugateAlgebraic_ne_zero.mpr hz
  · exact hz

/-- Actual finite attachment coefficients, inside the original algebraic field. -/
theorem attachmentSequence_diagonal_apply {m n : ℕ} (ports : Fin m → Fin n)
    (z : Fin m → AlgebraicComplex) (f : Signature AlgebraicComplex n) (x : Fin n → Bool) :
    HighHeightNormalization.attachmentSequence ports
      (fun j => HighHeightNormalization.algebraicBinary (z j)) f x =
      (∏ j, algebraicMatingWeight (z j) (x (ports j))) * f x := by
  apply Subtype.ext
  have hh := congrFun (HighHeightNormalization.attachmentSequence_coe ports z f) x
  rw [HighHeightNormalization.attachFamily_apply] at hh
  refine hh.trans ?_
  symm
  let φ : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom
  change φ ((∏ j, algebraicMatingWeight (z j) (x (ports j))) * f x) = _
  rw [map_mul,map_prod]
  change (∏ j, (algebraicMatingWeight (z j) (x (ports j)) : ℂ)) * (f x : ℂ) = _
  simp only [coe_algebraicMatingWeight]

/-- Matching reconstruction after actual algebraic normalization suffices for
matching of the original signature, with no change of coefficient field. -/
theorem attachmentSequence_matching_pullback {m n : ℕ} (ports : Fin m → Fin n)
    (z : Fin m → AlgebraicComplex) (hz : ∀ j, z j ≠ 0) (f : Signature AlgebraicComplex n)
    (h : WeightedMatching.IsProduct (HighHeightNormalization.attachmentSequence ports
      (fun j => HighHeightNormalization.algebraicBinary (z j)) f)) :
    WeightedMatching.IsProduct f := by
  let w := collectedDiagonal ports (fun j => algebraicMatingWeight (z j))
  apply (isWeighted_iff_isProduct f).mp
  apply diagonal_matching_pullback w
    (collectedDiagonal_ne_zero ports _ (fun j b => algebraicMatingWeight_ne_zero (hz j) b)) f
  have he : (fun x => (∏ i, w i (x i)) * f x) =
      HighHeightNormalization.attachmentSequence ports
        (fun j => HighHeightNormalization.algebraicBinary (z j)) f := by
    funext x
    rw [attachmentSequence_diagonal_apply]
    exact congrArg (fun t => t*f x) (collectedDiagonal_product ports _ x)
  rw [he]
  exact (isWeighted_iff_isProduct _).mpr h

/-- A complex literal-X reconstruction of an algebraic tensor has an algebraic
scalar: it is its actual coefficient at the all-first-false transversal. -/
theorem algebraic_isX_isProduct {n : ℕ} (f : Signature AlgebraicComplex n)
    (h : IsX (fun x => (f x : ℂ))) : WeightedMatching.IsProduct f := by
  classical
  obtain ⟨P,c,hc,hform⟩ := h
  let a := f (word P (fun _ => false))
  have ha : (a : ℂ) = c := by
    have hh := congrFun hform (word P (fun _ => false))
    simpa only [literal_word,mul_one] using hh
  have ha0 : a ≠ 0 := by
    intro hz
    have hh : (a : ℂ) = 0 := by rw [hz]; rfl
    exact hc (ha.symm.trans hh)
  apply (isWeighted_iff_isProduct f).mp
  refine ⟨P,(fun _ => 1),(fun _ => 1),a,ha0,(fun _ => one_ne_zero),(fun _ => one_ne_zero),?_⟩
  funext x
  apply Subtype.ext
  have hh := congrFun hform x
  rw [← ha] at hh
  refine hh.trans ?_
  rw [product_eq_literal P (fun _ => (1 : AlgebraicComplex)) a]
  simp only [Finset.prod_const_one,mul_one]
  by_cases hx : CommonPhase.Transversal P x <;> simp [literal,hx]

/-- The complete §8 normalization/reconstruction bridge used by a relative EO
induction: normalized complex IsX gives original algebraic B_× membership. -/
theorem normalized_isX_matching_pullback {m n : ℕ} (ports : Fin m → Fin n)
    (z : Fin m → AlgebraicComplex) (hz : ∀ j, z j ≠ 0) (f : Signature AlgebraicComplex n)
    (h : IsX (HighHeightNormalization.attachFamily ports (fun j => (z j : ℂ))
      (fun x => (f x : ℂ)))) : WeightedMatching.IsProduct f := by
  apply attachmentSequence_matching_pullback ports z hz f
  apply algebraic_isX_isProduct
  rw [HighHeightNormalization.attachmentSequence_coe]
  exact h

end Paper2.RelativeEO
