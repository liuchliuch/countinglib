import Paper2.Certificates.Q6LoopOrder
import Paper2.Certificates.Q6Action

/-! Naturality of the actual one-copy X-loop array under every verified
six-port relabeling and global complement. -/
namespace Paper2.Certificates.Q6

open Coverage

def LoopSpec.map (s : LoopSpec) (p : Equiv.Perm Port) : LoopSpec :=
  ⟨p s.first,p s.second,fun j => p (s.residual j)⟩

theorem ValidLoopSpec.map {s : LoopSpec} (hs : ValidLoopSpec s) (p : Equiv.Perm Port) :
    ValidLoopSpec (s.map p) := by
  refine ⟨fun h => hs.1 (p.injective h),p.injective.comp hs.2.1,?_⟩
  change Finset.univ.image (p ∘ s.residual) = _
  rw [← Finset.image_image,hs.2.2,Finset.image_sdiff _ _ p.injective,image_univ_perm]
  simp only [LoopSpec.map,Finset.image_insert,Finset.image_singleton]

theorem LoopSpec.map_chosen (s : LoopSpec) (p : Equiv.Perm Port) (e : Fin 6) :
    loopChosen (s.map p) e = (loopChosen s e).image p := by
  simp only [loopChosen,LoopSpec.map,Finset.image_image,Function.comp_def]

theorem loopChosen_subset (s : LoopSpec) (hs : ValidLoopSpec s) (e : Fin 6) :
    loopChosen s e ⊆ Finset.univ \ {s.first,s.second} := by
  rw [← hs.2.2]
  exact Finset.image_subset_image (Finset.filter_subset _ _)

theorem loopChosen_complement (s : LoopSpec) (hs : ValidLoopSpec s) (e : Fin 6) :
    loopChosen s (entryComplement e) =
      (Finset.univ \ {s.first,s.second}) \ loopChosen s e := by
  change (entrySet (entryComplement e)).image s.residual = _
  rw [entrySet_complement,Finset.image_sdiff _ _ hs.2.1,hs.2.2]
  rfl

theorem complement_insert_loop (p q : Port) (hpq : p ≠ q) (S : PortSet)
    (hs : S ⊆ Finset.univ \ {p,q}) :
    Finset.univ \ insert p S = insert q ((Finset.univ \ {p,q}) \ S) := by
  ext v
  have hv : v ∈ S → v ≠ p ∧ v ≠ q := by
    intro h
    simpa only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,
      Finset.mem_singleton,true_and,not_or] using hs h
  simp only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,
    Finset.mem_singleton,true_and,not_or]
  constructor
  · rintro ⟨hp,hS⟩
    by_cases hq : v = q
    · exact Or.inl hq
    · exact Or.inr ⟨⟨hp,hq⟩,hS⟩
  · rintro (rfl | ⟨⟨hp,_⟩,hS⟩)
    · exact ⟨Ne.symm hpq,fun h => (hv h).2 rfl⟩
    · exact ⟨hp,hS⟩

theorem actSet_insert_first (s : LoopSpec) (hs : ValidLoopSpec s)
    (p : Equiv.Perm Port) (c : Bool) (e : Fin 6) :
    actSet p c (insert s.first (loopChosen s e)) =
      if c then insert (s.map p).second (loopChosen (s.map p) (entryComplement e))
      else insert (s.map p).first (loopChosen (s.map p) e) := by
  cases c
  · change (insert s.first (loopChosen s e)).image p = _
    rw [Finset.image_insert,← s.map_chosen p e]
    rfl
  · change Finset.univ \ (insert s.first (loopChosen s e)).image p = _
    rw [Finset.image_insert,← s.map_chosen p e]
    change Finset.univ \ insert (s.map p).first (loopChosen (s.map p) e) = _
    rw [complement_insert_loop _ _ (hs.map p).1 _ (loopChosen_subset _ (hs.map p) e)]
    rw [← loopChosen_complement _ (hs.map p) e]
    rfl

theorem actSet_insert_second (s : LoopSpec) (hs : ValidLoopSpec s)
    (p : Equiv.Perm Port) (c : Bool) (e : Fin 6) :
    actSet p c (insert s.second (loopChosen s e)) =
      if c then insert (s.map p).first (loopChosen (s.map p) (entryComplement e))
      else insert (s.map p).second (loopChosen (s.map p) e) := by
  cases c
  · change (insert s.second (loopChosen s e)).image p = _
    rw [Finset.image_insert,← s.map_chosen p e]
    rfl
  · change Finset.univ \ (insert s.second (loopChosen s e)).image p = _
    rw [Finset.image_insert,← s.map_chosen p e]
    change Finset.univ \ insert (s.map p).second (loopChosen (s.map p) e) = _
    have hsub : loopChosen (s.map p) e ⊆ Finset.univ \ {(s.map p).second,(s.map p).first} := by
      rw [Finset.pair_comm]
      exact loopChosen_subset _ (hs.map p) e
    rw [complement_insert_loop _ _ (Ne.symm (hs.map p).1) _ hsub,Finset.pair_comm]
    rw [← loopChosen_complement _ (hs.map p) e]
    rfl

variable {K : Type*} [CommRing K] [NoZeroDivisors K]

theorem loopArray_action (q : Fin 20 → K) (a : Action) (ha : a.Valid)
    (s : LoopSpec) (hs : ValidLoopSpec s) :
    loopArray (fun i => q (a.coords i)) s =
      if a.complement then
        (fun e => loopArray q (s.map (a.portEquiv ha)) (entryComplement e))
      else loopArray q (s.map (a.portEquiv ha)) := by
  funext e
  unfold loopArray loopMasks
  rw [coefficient_action q a ha,coefficient_action q a ha]
  rw [actSet_insert_first s hs,actSet_insert_second s hs]
  cases hc : a.complement
  · rfl
  · exact add_comm _ _

/-- The canonical fifteen-loop safety hypothesis is invariant under the
actual orbit action, including reversal of all six bits. -/
theorem AllLoopSafe.action (q : Fin 20 → K) (h : AllLoopSafe q)
    (a : Action) (ha : a.Valid) : AllLoopSafe (fun i => q (a.coords i)) := by
  intro i
  rw [loopArray_action q a ha _ (valid_loopSpecs i)]
  have hs := AllLoopSafe.of_valid q h ((loopSpecs i).map (a.portEquiv ha))
    ((valid_loopSpecs i).map (a.portEquiv ha))
  cases hc : a.complement
  · exact hs
  · exact hs.complement

end Paper2.Certificates.Q6
