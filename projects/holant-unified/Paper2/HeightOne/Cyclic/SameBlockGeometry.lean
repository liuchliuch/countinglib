import Paper2.HeightOne.Cyclic.DiagonalCardSupport

/-! Closing one complete matching block leaves a genuine perfect matching on
the undeleted named ports. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open EndpointSelfLoop

abbrev sameRemaining {n : ℕ} (P : Pairing n) (i : Fin P.count) :=
  Remaining (P.ports (i, false)) (P.ports (i, true))

lemma same_distinct {n : ℕ} (P : Pairing n) (i : Fin P.count) :
    P.ports (i, false) ≠ P.ports (i, true) := by simp

def sameMate {n : ℕ} (P : Pairing n) (i : Fin P.count) (x : sameRemaining P i) : sameRemaining P i :=
  ⟨pairingMate P x.val, by
    intro h
    have he := congrArg (pairingMate P) h
    simp only [pairingMate_pairingMate, pairingMate_port, Bool.not_false] at he
    exact x.property.2 he,
   by
    intro h
    have he := congrArg (pairingMate P) h
    simp only [pairingMate_pairingMate, pairingMate_port, Bool.not_true] at he
    exact x.property.1 he⟩

@[simp] lemma sameMate_sameMate {n : ℕ} (P : Pairing n) (i : Fin P.count) (x : sameRemaining P i) :
    sameMate P i (sameMate P i x) = x := by
  apply Subtype.ext
  exact pairingMate_pairingMate P x.val

def sameFreeMatching {n : ℕ} (P : Pairing n) (i : Fin P.count) :
    FreeMatching (Fin (Fintype.card (sameRemaining P i))) where
  mate k := (Fintype.equivFin (sameRemaining P i)) (sameMate P i ((Fintype.equivFin (sameRemaining P i)).symm k))
  involutive k := by simp
  ne k h := by
    have he := congrArg (Fintype.equivFin (sameRemaining P i)).symm h
    simp only [Equiv.symm_apply_apply] at he
    exact pairingMate_ne P _ (congrArg Subtype.val he)

def samePairing {n : ℕ} (P : Pairing n) (i : Fin P.count) :
    Pairing (Fintype.card (sameRemaining P i)) := pairingOfInvolution (sameFreeMatching P i)

lemma samePairing_mate {n : ℕ} (P : Pairing n) (i : Fin P.count) (k : Fin (Fintype.card (sameRemaining P i))) :
    pairingMate (samePairing P i) k = (Fintype.equivFin (sameRemaining P i))
      (sameMate P i ((Fintype.equivFin (sameRemaining P i)).symm k)) := pairingOfInvolution_mate _ _

@[simp] lemma blockWord_mate {n : ℕ} (P : Pairing n) (t : Fin P.count → Bool) (k : Fin n) :
    blockWord P t (pairingMate P k) = blockWord P t k := by
  obtain ⟨⟨j, b⟩, rfl⟩ := P.ports.surjective k
  simp only [pairingMate_port]
  exact (blockWord_port P t j (!b)).trans (blockWord_port P t j b).symm

def sameResidualWord {n : ℕ} (P : Pairing n) (i : Fin P.count) (t : Fin P.count → Bool) :
    Fin (Fintype.card (sameRemaining P i)) → Bool :=
  fun k => blockWord P t ((Fintype.equivFin (sameRemaining P i)).symm k).val

lemma sameResidualWord_mem {n : ℕ} (P : Pairing n) (i : Fin P.count) (t : Fin P.count → Bool) :
    sameResidualWord P i t ∈ equalityCode (samePairing P i) := by
  rw [mem_equalityCode_iff_mate]
  intro k
  rw [samePairing_mate]
  simp only [sameResidualWord, Equiv.symm_apply_apply, sameMate]
  exact blockWord_mate P t _

lemma same_lift_mem {n : ℕ} (P : Pairing n) (i : Fin P.count)
    (x : Fin (Fintype.card (sameRemaining P i)) → Bool) (b : Bool)
    (hx : extendBits (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i)
      (fun k => x ((Fintype.equivFin (sameRemaining P i)) k)) b b ∈ equalityCode P) :
    x ∈ equalityCode (samePairing P i) := by
  let E := Fintype.equivFin (sameRemaining P i)
  rw [mem_equalityCode_iff_mate]
  intro k
  rw [samePairing_mate]
  have hm := (mem_equalityCode_iff_mate P _).mp hx (E.symm k).val
  have hleft := extendBits_remaining (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i)
    (fun k => x (E k)) b b (sameMate P i (E.symm k))
  have hright := extendBits_remaining (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i)
    (fun k => x (E k)) b b (E.symm k)
  have h := hleft.symm.trans (hm.trans hright)
  simpa only [E, Equiv.apply_symm_apply] using h

/-- Any nonzero same-block card has the full inherited matching support. -/
theorem same_card_support_eq {K : Type*} [Field K] {n : ℕ} (f : Signature K n) (P : Pairing n)
    (hF : support f ⊆ equalityCode P) (i : Fin P.count) (s : K)
    (hc : EqualityMatchingSupport (plusContraction (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i) s f)) :
    support (Tensor.reindex (Fintype.equivFin (sameRemaining P i))
      (plusContraction (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i) s f)) =
      equalityCode (samePairing P i) := by
  obtain ⟨Q, hQ⟩ := hc
  apply Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    rw [mem_support, Tensor.reindex_apply, plusContraction_apply] at hx
    by_cases h0 : f (extendBits (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i)
        (fun k => x ((Fintype.equivFin (sameRemaining P i)) k)) false false) ≠ 0
    · exact same_lift_mem P i x false (hF ((mem_support _ _).mpr h0))
    · have h1 : f (extendBits (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i)
          (fun k => x ((Fintype.equivFin (sameRemaining P i)) k)) true true) ≠ 0 := by
        intro he
        exact hx (by simp [not_ne_iff.mp h0, he])
      exact same_lift_mem P i x true (hF ((mem_support _ _).mpr h1))
  · rw [hQ, equalityCode_card, equalityCode_card]

end
end Paper2.HeightOne.Cyclic
