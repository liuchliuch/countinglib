import Paper2.HeightOne.Cyclic.MatchingCompletion

/-! A fixed-point-free involution on the original finite ordered ports gives
an explicit ordered perfect pairing. No existence of a matching is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section

@[simp] lemma FreeMatching.mate_mate {ι : Type} (M : FreeMatching ι) (i : ι) :
    M.mate (M.mate i) = i := M.involutive i

abbrev lowerPorts {n : ℕ} (M : FreeMatching (Fin n)) := {i : Fin n // i < M.mate i}

instance {n : ℕ} (M : FreeMatching (Fin n)) : Fintype (lowerPorts M) := by
  classical
  exact Subtype.fintype _

def matchingPortMap {n : ℕ} (M : FreeMatching (Fin n)) : lowerPorts M × Bool → Fin n :=
  fun p => if p.2 then M.mate p.1.val else p.1.val

lemma matchingPortMap_bijective {n : ℕ} (M : FreeMatching (Fin n)) :
    Function.Bijective (matchingPortMap M) := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ he
    cases a <;> cases b
    · have hij : i = j := Subtype.ext he
      simpa using hij
    · change i.val = M.mate j.val at he
      have hm : M.mate i.val = j.val := by rw [he, FreeMatching.mate_mate]
      have hi := i.property
      have hj := j.property
      rw [he, FreeMatching.mate_mate] at hi
      exact False.elim ((not_lt_of_ge hj.le) hi)
    · change M.mate i.val = j.val at he
      have hm : M.mate j.val = i.val := by rw [← he, FreeMatching.mate_mate]
      have hi := i.property
      have hj := j.property
      rw [← he, FreeMatching.mate_mate] at hj
      exact False.elim ((not_lt_of_ge hi.le) hj)
    · have hij : i = j := Subtype.ext (M.injective he)
      simpa using hij
  · intro i
    rcases lt_or_gt_of_ne (M.ne i) with hi | hi
    · refine ⟨(⟨M.mate i, ?_⟩, true), ?_⟩
      · simpa only [FreeMatching.mate_mate] using hi
      · simp [matchingPortMap]
    · exact ⟨(⟨i, hi⟩, false), rfl⟩

def pairingOfInvolution {n : ℕ} (M : FreeMatching (Fin n)) : Pairing n where
  count := Fintype.card (lowerPorts M)
  ports := (Equiv.prodCongr (Fintype.equivFin (lowerPorts M)).symm (Equiv.refl Bool)).trans
    (Equiv.ofBijective (matchingPortMap M) (matchingPortMap_bijective M))

lemma pairingOfInvolution_mate {n : ℕ} (M : FreeMatching (Fin n)) (i : Fin n) :
    pairingMate (pairingOfInvolution M) i = M.mate i := by
  obtain ⟨⟨j, b⟩, rfl⟩ := (pairingOfInvolution M).ports.surjective i
  rw [pairingMate_port]
  cases b <;> simp [pairingOfInvolution, matchingPortMap]

/-- A symmetric relation with exactly one neighbour at every port supplies an
actual pairing, with the original relation on every displayed pair. -/
theorem pairing_of_unique_neighbours {n : ℕ} (R : Fin n → Fin n → Prop)
    (hsymm : Symmetric R) (hirr : ∀ u, ¬ R u u)
    (hunique : ∀ u v w, R u v → R u w → v = w) (htotal : ∀ u, ∃ v, R u v) :
    ∃ P : Pairing n, ∀ i, R (P.ports (i, false)) (P.ports (i, true)) := by
  classical
  choose m hm using htotal
  let M : FreeMatching (Fin n) := {
    mate := m
    involutive := fun i => hunique (m i) (m (m i)) i (hm (m i)) (hsymm (hm i))
    ne := fun i hi => by
      have h := hm i
      rw [hi] at h
      exact hirr i h }
  refine ⟨pairingOfInvolution M, ?_⟩
  intro i
  have h := hm ((pairingOfInvolution M).ports (i, false))
  change R _ (M.mate _) at h
  rw [← pairingOfInvolution_mate, pairingMate_port] at h
  exact h

end
end Paper2.HeightOne.Cyclic
