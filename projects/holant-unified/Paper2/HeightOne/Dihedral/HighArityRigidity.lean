import Paper2.HeightOne.Dihedral.HighArityCards

/-! Matching independence at arity at least eight. Simultaneous localization
uses only one fixed specified kernel on the original ancestor. Its first card
is a genuine matching product, so all subsequent cards remain such products.
The terminal six-port ancestor cannot have disagreeing four-port matchings. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Holant Holant.Marked Holant.Certificates
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.TwoCardLocalization
open Holant.Dihedral.CompatibleClosure (pairOrder)
set_option backward.isDefEq.respectTransparency false

private theorem pairOrder_zero_one {n : ℕ} : pairOrder (0 : Fin (n+2)) 1 = Equiv.refl _ := by
  simp [pairOrder]

theorem matching_contract {n : ℕ} (C : Mat) (hC : IsMonomial C)
    (q : Signature Scalar (n+2)) (hq : MatchingOrZero monomialGroup q) :
    MatchingOrZero monomialGroup (Signature.contract C q) := by
  have h := (contractPair_closed monomial_matrix_group monomial_X monomial_reversal
    (0 : Fin (n+2)) 1 Fin.zero_ne_one C ((safe_monomial_iff C).mpr hC) q hq).reindex
    (remainingOrder (0 : Fin (n+2)) 1 Fin.zero_ne_one).symm
  rw [contractPair_order] at h
  simpa only [pairOrder_zero_one,Equiv.refl_symm,Tensor.reindex_refl] using h

theorem Program.core_matching (C : Mat) (hC : IsMonomial C)
    {n m : ℕ} (P : Program Unit n m) (q : Signature Scalar (n+2))
    (hq : MatchingOrZero monomialGroup q) :
    MatchingOrZero monomialGroup (P.core (fun _ => C) q) := by
  induction P with
  | done n => exact hq
  | step p i rest ih =>
    exact ih _ (matching_contract C hC _ (hq.reindex (outsideOrder p).symm))

/-- One or more residual instructions make the original ancestor a matching
product from its literal first contracted table. No field of graph outputs is
replaced by a supplied closure proposition. -/
theorem Program.core_matching_of_first_cards (C : Mat) (hC : IsMonomial C)
    {n m : ℕ} (P : Program Unit n m) (hlen : 0 < P.length)
    (q : Signature Scalar (n+2))
    (hcards : ∀ p : Equiv.Perm (Fin (n+2)),
      MatchingOrZero monomialGroup (Signature.contract C (Tensor.reindex p.symm q))) :
    MatchingOrZero monomialGroup (P.core (fun _ => C) q) := by
  cases P with
  | done n => simp [Program.length] at hlen
  | step p i rest =>
    exact Program.core_matching C hC rest _ (hcards (outsideOrder p))

/-- The same literal closure for a labelled family of available kernels. -/
theorem Program.core_matching_family {I : Type*} (C : I → Mat)
    (hC : ∀ i, IsMonomial (C i)) {n m : ℕ} (P : Program I n m)
    (q : Signature Scalar (n+2)) (hq : MatchingOrZero monomialGroup q) :
    MatchingOrZero monomialGroup (P.core C q) := by
  induction P with
  | done n => exact hq
  | step p i rest ih =>
    exact ih _ (matching_contract (C i) (hC i) _ (hq.reindex (outsideOrder p).symm))

theorem Program.core_matching_family_of_first_cards {I : Type*} (C : I → Mat)
    (hC : ∀ i, IsMonomial (C i)) {n m : ℕ} (P : Program I n m)
    (hlen : 0 < P.length) (q : Signature Scalar (n+2))
    (hcards : ∀ i (p : Equiv.Perm (Fin (n+2))),
      MatchingOrZero monomialGroup (Signature.contract (C i) (Tensor.reindex p.symm q))) :
    MatchingOrZero monomialGroup (P.core C q) := by
  cases P with
  | done n => simp [Program.length] at hlen
  | step p i rest =>
    exact Program.core_matching_family C hC rest _ (hcards i (outsideOrder p))

/-- Literal high-arity matching rigidity. The two selected kernels can be any
available phases in the original pencil. The only surgery kernel is `C`. -/
theorem no_different_matching_cards
    (r : ℕ) (hr : 1 ≤ r) (q : Signature Scalar (2*r+6))
    (C : Mat) (hC : IsMonomial C)
    (hcards : ∀ p : Equiv.Perm (Fin (2*r+6)),
      MatchingOrZero monomialGroup (Signature.contract C (Tensor.reindex p.symm q)))
    (C₀ C₁ : Mat) (hC₀ : IsMonomial C₀) (hC₁ : IsMonomial C₁) :
    ¬ DifferentProducts monomialGroup (2*r+4)
      (Signature.contract C₀ q) (Signature.contract C₁ q) := by
  intro hd
  obtain ⟨P,hP,hout⟩ := different_matching_program C hC r _ _ hd
  have hanc := Program.core_matching_of_first_cards C hC P (by rw [hP]; omega) q hcards
  rw [← P.inherited_card,← P.inherited_card] at hout
  have hn₀ : Signature.contract C₀ (P.core (fun _ => C) q) ≠ 0 := by
    obtain ⟨M₀,M₁,hM₀,hM₁,hc₀,hc₁,hq₀,hq₁,hne⟩ := hout
    rw [hq₀]
    exact productValue_nonzero M₀.ports M₀.matrix M₀.scalar
      (fun e => SafeBinary.nonsingular monomial_matrix_group (hM₀ e)) hc₀
  have hn₁ : Signature.contract C₁ (P.core (fun _ => C) q) ≠ 0 := by
    obtain ⟨M₀,M₁,hM₀,hM₁,hc₀,hc₁,hq₀,hq₁,hne⟩ := hout
    rw [hq₁]
    exact productValue_nonzero M₁.ports M₁.matrix M₁.scalar
      (fun e => SafeBinary.nonsingular monomial_matrix_group (hM₁ e)) hc₁
  exact different_not_common hout (matching_cards_common _ hanc C₀ C₁ hC₀ hC₁ hn₀ hn₁)

end
end Paper2.HeightOne.Dihedral.HighArity
