import Paper2.Certificates.Q6Entry
import Mathlib.Data.Fintype.EquivFin

/-! The fifteen canonical loops represent every ordered choice of two internal
ports and every ordering of the four remaining boundary ports. -/
namespace Paper2.Certificates.Q6

def ValidLoopSpec (s : LoopSpec) : Prop :=
  s.first ≠ s.second ∧ Function.Injective s.residual ∧
    Finset.univ.image s.residual = Finset.univ \ {s.first,s.second}

theorem valid_loopSpecs (i : Fin 15) : ValidLoopSpec (loopSpecs i) :=
  ⟨ne_of_lt (loop_specs_valid i).1,(loop_specs_valid i).2.1.injective,
    (loop_specs_valid i).2.2⟩

/-- Equal finite injective enumerations differ by a genuine port permutation. -/
theorem permutation_of_image_eq {n : ℕ} (f g : Fin n → Port)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (he : Finset.univ.image f = Finset.univ.image g) :
    ∃ r : Equiv.Perm (Fin n), ∀ j, f j = g (r j) := by
  classical
  have hex : ∀ j, ∃ k, g k = f j := by
    intro j
    have hm : f j ∈ Finset.univ.image f := Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
    rw [he] at hm
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hm
    exact ⟨k,hk⟩
  let r : Fin n → Fin n := fun j => Classical.choose (hex j)
  have hr : ∀ j, g (r j) = f j := fun j => Classical.choose_spec (hex j)
  have hi : Function.Injective r := by
    intro i j hij
    apply hf
    rw [← hr i, ← hr j, hij]
  refine ⟨Equiv.ofBijective r ((Fintype.bijective_iff_injective_and_card r).mpr ⟨hi,rfl⟩), ?_⟩
  intro j
  exact (hr j).symm

theorem canonical_loop_of_valid (s : LoopSpec) (hs : ValidLoopSpec s) :
    ∃ i : Fin 15, (s.first = (loopSpecs i).first ∧ s.second = (loopSpecs i).second) ∨
      (s.first = (loopSpecs i).second ∧ s.second = (loopSpecs i).first) := by
  rcases lt_or_gt_of_ne hs.1 with h | h
  · obtain ⟨i,hi⟩ := loop_pairs_complete s.first s.second h
    exact ⟨i,Or.inl ⟨hi.1.symm,hi.2.symm⟩⟩
  · obtain ⟨i,hi⟩ := loop_pairs_complete s.second s.first h
    exact ⟨i,Or.inr ⟨hi.2.symm,hi.1.symm⟩⟩

variable {K : Type*} [CommRing K] [NoZeroDivisors K]

/-- No boundary ordering or orientation is omitted by the canonical loop deck. -/
theorem AllLoopSafe.of_valid (q : Fin 20 → K) (h : AllLoopSafe q)
    (s : LoopSpec) (hs : ValidLoopSpec s) : NecessarySafe (loopArray q s) := by
  obtain ⟨i,hi⟩ := canonical_loop_of_valid s hs
  have himage : Finset.univ.image s.residual = Finset.univ.image (loopSpecs i).residual := by
    rw [hs.2.2,(loop_specs_valid i).2.2]
    rcases hi with hi | hi
    · rw [hi.1,hi.2]
    · rw [hi.1,hi.2,Finset.pair_comm]
  obtain ⟨r,hr⟩ := permutation_of_image_eq s.residual (loopSpecs i).residual hs.2.1
    (loop_specs_valid i).2.1.injective himage
  have chosen : ∀ e, loopChosen s e = loopChosen (loopSpecs i) (entryPerm r e) := by
    intro e
    change (entrySet e).image s.residual = (entrySet (entryPerm r e)).image (loopSpecs i).residual
    rw [entrySet_entryPerm,Finset.image_image]
    congr 1
    funext j
    exact hr j
  have hv : loopArray q s = fun e => loopArray q (loopSpecs i) (entryPerm r e) := by
    funext e
    unfold loopArray loopMasks
    rw [chosen e]
    rcases hi with hi | hi
    · rw [hi.1,hi.2]
    · rw [hi.1,hi.2]
      exact add_comm _ _
  rw [hv]
  exact (h i).boundary_reindex r

end Paper2.Certificates.Q6
