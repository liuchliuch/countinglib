import Paper2.HighHeightNormalization.HighArityRoute
import Paper2.SourceFaithful.TransversalCube

/-! Original-language high-arity endpoint under the source-faithful effective
number-field output convention. Reconstruction and algebraic scalar recovery
are reused as pure mathematics, with actual reduction transport rebuilt. -/
namespace Paper2.SourceFaithful.HighHeight
open MatchingPropagation CommonPhase EndpointSelfLoop Paper2.HighHeightReconstruction
open Paper2.HighHeightNormalization Tractable ExactInput
variable {n : ℕ}

/-- An actual finite algebraic language containing the normalized complete
mountain is hard at every arity at least ten. The central tensor is never
adjoined as a separate signature. -/
theorem normalized_mountain_hard
    (DG : Paper1DirectGadgetAccepted) (R : Paper1RestrictionAccepted) (EO : Paper1EOAccepted)
    (L : Language) (hn : 10 ≤ n) (M F : Signature AlgebraicComplex n)
    (a b : AlgebraicComplex) (hab : a*b ≠ 0) (hF : Tensor.ChargeLayer F 0)
    (lam : PortPair (Fin n) → ℂ)
    (P : (e : PortPair (Fin n)) → Matching (Remaining e.first e.second))
    (hdeck : MatchingDeck (fun x => (F x : ℂ)) lam P) (hnz : ∀ e, lam e ≠ 0)
    (hM : ∀ x, M x = (if x = (fun _ => false) then a else 0) +
      (if x = (fun _ => true) then b else 0) + F x)
    (hmem : (⟨n,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  have hFc : Tensor.ChargeLayer (fun x => (F x : ℂ)) 0 := by
    intro x hx
    apply hF x
    intro hz
    apply hx
    change (F x : ℂ) = 0
    rw [hz]
    rfl
  have hX := reconstruct_ge_ten (by simpa using hn) (fun x => (F x : ℂ)) hFc lam P hdeck hnz
  obtain ⟨Q,c,hc,hQ⟩ := algebraic_product_of_literal F hX
  have hcount : 3 ≤ Q.count := by
    have hcard := Fintype.card_congr Q.ports
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hcard
    omega
  have hM' : M = TransversalCube.sourceMountain Q a b c (fun _ => 1) (fun _ => 1) := by
    funext x
    rw [hM,hQ]
    rfl
  rw [hM'] at hmem
  exact TransversalCube.matching_mountain_hard DG R EO L Q hcount a b c
    (fun _ => 1) (fun _ => 1) hab (by simpa using hc) hmem

/-- The actual backward reduction from a finite retained normalization
extension transports hardness to the original canonical-field input language. -/
theorem normalized_mountain_hard_original
    (DG : Paper1DirectGadgetAccepted) (R : Paper1RestrictionAccepted) (EO : Paper1EOAccepted)
    (L N : Language) (hNL : FixedFieldOutput.Reduces .nativeX N L)
    (hn : 10 ≤ n) (M F : Signature AlgebraicComplex n)
    (a b : AlgebraicComplex) (hab : a*b ≠ 0) (hF : Tensor.ChargeLayer F 0)
    (lam : PortPair (Fin n) → ℂ)
    (P : (e : PortPair (Fin n)) → Matching (Remaining e.first e.second))
    (hdeck : MatchingDeck (fun x => (F x : ℂ)) lam P) (hnz : ∀ e, lam e ≠ 0)
    (hM : ∀ x, M x = (if x = (fun _ => false) then a else 0) +
      (if x = (fun _ => true) then b else 0) + F x)
    (hmem : (⟨n,M⟩ : AnySignature AlgebraicComplex) ∈ N.family) :
    FixedFieldOutput.SharpPHard .nativeX L :=
  (normalized_mountain_hard DG R EO N hn M F a b hab hF lam P hdeck hnz hM hmem).transport
    hNL

/-- Height d≥5, once the finite normalization extension is constructed. This
is a proved machine-reduction endpoint, not an accepted normalization theorem. -/
theorem height_ge_five_normalized_route
    (DG : Paper1DirectGadgetAccepted) (R : Paper1RestrictionAccepted) (EO : Paper1EOAccepted)
    (L N : Language) (hNL : FixedFieldOutput.Reduces .nativeX N L)
    {d : ℕ} (hd : 5 ≤ d) (M F : Signature AlgebraicComplex (2*d))
    (a b : AlgebraicComplex) (hab : a*b ≠ 0) (hF : Tensor.ChargeLayer F 0)
    (lam : PortPair (Fin (2*d)) → ℂ)
    (P : (e : PortPair (Fin (2*d))) → Matching (Remaining e.first e.second))
    (hdeck : MatchingDeck (fun x => (F x : ℂ)) lam P) (hnz : ∀ e, lam e ≠ 0)
    (hM : ∀ x, M x = (if x = (fun _ => false) then a else 0) +
      (if x = (fun _ => true) then b else 0) + F x)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ N.family) :
    FixedFieldOutput.SharpPHard .nativeX L :=
  normalized_mountain_hard_original DG R EO L N hNL (by omega) M F a b hab hF
    lam P hdeck hnz hM hmem

end Paper2.SourceFaithful.HighHeight

