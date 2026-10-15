import Paper2.Certificates.Q8AlgebraicReconstruction
import Paper2.SourceFaithful.HeightFour.Canonical
import Paper2.SourceFaithful.HighHeightReconstruction

/-! The actual normalized complete height-four mountain is classified through
the exhaustive atlas. A collision gives the matching-mountain graph; the other
case reconstructs the labelled algebraic RM coefficients and its Bell endpoint. -/
namespace Paper2.SourceFaithful.HeightFour
open Tractable ExactInput CommonPhase EndpointSelfLoop MatchingPropagation
open HighHeightReconstruction Paper2.HighHeightNormalization Certificates.Q8.Atlas
open ReedMullerNormalization BellReduction

private theorem member_network {n : ℕ} {F : SignatureFamily AlgebraicComplex}
    {f : Signature AlgebraicComplex n}
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ F) : NetworkRealizable F f := by
  let e : (Σ _ : Unit, Fin n) ≃ Fin n := {
    toFun := fun p => p.2
    invFun := fun i => ⟨(),i⟩
    left_inv := by rintro ⟨u,i⟩; cases u; rfl
    right_inv := fun _ => rfl }
  have h := NetworkRealizable.piTensor (F := F) (fun _ : Unit => n) (fun _ => f) (fun _ => hf)
  have hh := h.reindex e
  have heq : Tensor.reindex e (Tensor.piTensor (fun _ : Unit => f)) = f := by
    funext x
    simp [Tensor.reindex,Tensor.piTensor,e]
  exact heq ▸ hh

theorem central_weight_of_charge (F : Signature AlgebraicComplex 8)
    (hF : Tensor.ChargeLayer F 0) :
    ∀ x, ReedMuller.weight x ≠ 4 → F x = 0 := by
  intro x hx
  by_contra hn
  have hh := (doubledCharge_eq_zero_iff x).mp (hF x hn)
  have hw : Paper2.weight x = ReedMuller.weight x := by
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> rfl
  simp only [Fintype.card_fin,hw] at hh
  omega

theorem labeled_endpoint_word (p : Equiv.Perm (Fin 8)) (x : Fin 8 → Bool) (b : Bool) :
    (fun v => x (p v)) = (fun _ => b) ↔ x = (fun _ => b) := by
  constructor
  · intro h
    funext v
    simpa using congrFun h (p.symm v)
  · rintro rfl
    rfl

theorem labeled_mountain_source
    (p : Equiv.Perm (Fin 8)) (M F : Signature AlgebraicComplex 8)
    (A B c : AlgebraicComplex)
    (hM : ∀ x, M x = (if x = (fun _ => false) then A else 0) +
      (if x = (fun _ => true) then B else 0) + F x)
    (hF : labeledTensor p F = fun x => c * ReedMuller.central x) :
    labeledTensor p M = source A B c := by
  funext x
  change M (fun v => x (p v)) = _
  rw [hM]
  simp only [labeled_endpoint_word,source]
  rw [show F (fun v => x (p v)) = c * ReedMuller.central x from congrFun hF x]
  rfl

/-- The actual complete height-four mountain endpoint. Every hypothesis about
the finite matching deck concerns actual contractions of the central table;
the atlas conclusion and both complexity exits are proved internally. -/
theorem normalized_mountain_hard
    (P1 : Paper1Accepted) (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (Fac : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (N : Paper1NormalizationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hHigh : HighCharge L.family) (hnot : ¬ Tract (kImage L))
    (M F : Signature AlgebraicComplex 8) (A B : AlgebraicComplex)
    (hab : A * B ≠ 0) (hF : Tensor.ChargeLayer F 0)
    (lam : PortPair (Fin 8) → ℂ)
    (P : (e : PortPair (Fin 8)) → MatchingPropagation.Matching (EndpointSelfLoop.Remaining e.first e.second))
    (hdeck : MatchingDeck (fun x => (F x : ℂ)) lam P) (hnz : ∀ e, lam e ≠ 0)
    (hM : ∀ x, M x = (if x = (fun _ => false) then A else 0) +
      (if x = (fun _ => true) then B else 0) + F x)
    (hmem : (⟨8,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases hc : MatchingFamilyCollisionFree (indexedMatching P)
  · obtain ⟨p,c,hc,he⟩ := collision_free_deck_reedMuller_algebraic F lam P hdeck hnz hc
      (central_weight_of_charge F hF)
    have hr : NetworkRealizable L.family (source A B c) := by
      have h := (member_network hmem).reindex p
      change NetworkRealizable L.family (labeledTensor p M) at h
      rw [labeled_mountain_source p M F A B c hM he] at h
      exact h
    exact canonical_realized_hard P1 G O Fac U E R N L hpre hboth hHigh hnot A B c hab hc hr
  · have hFc : Tensor.ChargeLayer (fun x => (F x : ℂ)) 0 := by
      intro x hx
      exact hF x (fun hz => hx (by change (F x : ℂ) = 0; rw [hz]; rfl))
    have hX := matching_deck_of_collision (fun x => (F x : ℂ)) hFc lam P hdeck hnz hc
    obtain ⟨Q,c,hc,hQ⟩ := algebraic_product_of_literal F hX
    have hcount : 3 ≤ Q.count := by
      have hcard := Fintype.card_congr Q.ports
      simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hcard
      omega
    have hM' : M = Paper2.TransversalCube.sourceMountain Q A B c (fun _ => 1) (fun _ => 1) := by
      funext x
      rw [hM,hQ]
      rfl
    rw [hM'] at hmem
    exact TransversalCube.matching_mountain_hard G R E L Q hcount A B c
      (fun _ => 1) (fun _ => 1) hab (by simpa using hc) hmem

theorem normalized_mountain_classification
    (P1 : Paper1Accepted) (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (Fac : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (N : Paper1NormalizationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hHigh : HighCharge L.family)
    (M F : Signature AlgebraicComplex 8) (A B : AlgebraicComplex)
    (hab : A * B ≠ 0) (hF : Tensor.ChargeLayer F 0)
    (lam : PortPair (Fin 8) → ℂ)
    (P : (e : PortPair (Fin 8)) → MatchingPropagation.Matching (EndpointSelfLoop.Remaining e.first e.second))
    (hdeck : MatchingDeck (fun x => (F x : ℂ)) lam P) (hnz : ∀ e, lam e ≠ 0)
    (hM : ∀ x, M x = (if x = (fun _ => false) then A else 0) +
      (if x = (fun _ => true) then B else 0) + F x)
    (hmem : (⟨8,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases ht : Tract (kImage L)
  · exact Or.inl ht
  · exact Or.inr (normalized_mountain_hard P1 G O Fac U E R N L hpre hboth hHigh ht
      M F A B hab hF lam P hdeck hnz hM hmem)

end Paper2.SourceFaithful.HeightFour
