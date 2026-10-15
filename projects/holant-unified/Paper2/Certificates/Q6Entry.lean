import Paper2.Certificates.Q6SafetySymmetry
import Paper2.Certificates.Q6Arrays

/-! W₄ is exactly the set of two-element subsets of four ordered boundary
ports. Its port permutations preserve the complementary-entry relation. -/
namespace Paper2.Certificates.Q6

abbrev BoundarySet := Finset (Fin 4)

def entrySet (e : Fin 6) : BoundarySet :=
  Finset.univ.filter (fun j => eoWords e j = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem entrySet_card (e : Fin 6) : (entrySet e).card = 2 := by
  revert e
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem entrySet_injective : Function.Injective entrySet := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem entrySet_complete (S : BoundarySet) (h : S.card = 2) : ∃ e, entrySet e = S := by
  revert S
  decide +kernel

noncomputable def entryEquiv : Fin 6 ≃ {S : BoundarySet // S.card = 2} :=
  Equiv.ofBijective (fun e => ⟨entrySet e,entrySet_card e⟩) (by
    constructor
    · intro e f h
      exact entrySet_injective (congrArg Subtype.val h)
    · rintro ⟨S,hS⟩
      obtain ⟨e,he⟩ := entrySet_complete S hS
      exact ⟨e,Subtype.ext he⟩)

noncomputable def boundarySetPerm (r : Equiv.Perm (Fin 4)) :
    Equiv.Perm {S : BoundarySet // S.card = 2} where
  toFun S := ⟨S.val.image r, by rw [Finset.card_image_iff.mpr r.injective.injOn]; exact S.property⟩
  invFun S := ⟨S.val.image r.symm, by rw [Finset.card_image_iff.mpr r.symm.injective.injOn]; exact S.property⟩
  left_inv S := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, r.symm_apply_apply, Finset.image_id']
  right_inv S := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, r.apply_symm_apply, Finset.image_id']

noncomputable def entryPerm (r : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 6) :=
  entryEquiv.trans ((boundarySetPerm r).trans entryEquiv.symm)

theorem entrySet_entryPerm (r : Equiv.Perm (Fin 4)) (e : Fin 6) :
    entrySet (entryPerm r e) = (entrySet e).image r := by
  change (entryEquiv (entryEquiv.symm (boundarySetPerm r (entryEquiv e)))).val = _
  rw [entryEquiv.apply_symm_apply]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem entrySet_complement (e : Fin 6) :
    entrySet (entryComplement e) = Finset.univ \ entrySet e := by
  revert e
  decide +kernel

theorem entryPerm_complement (r : Equiv.Perm (Fin 4)) (e : Fin 6) :
    entryPerm r (entryComplement e) = entryComplement (entryPerm r e) := by
  apply entrySet_injective
  rw [entrySet_entryPerm, entrySet_complement, Finset.image_sdiff _ _ r.injective,
    entrySet_complement, entrySet_entryPerm]
  congr 1
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact ⟨r.symm j,r.apply_symm_apply j⟩

variable {K : Type*} [CommRing K] [NoZeroDivisors K]

theorem NecessarySafe.boundary_reindex {v : Fin 6 → K} (h : NecessarySafe v)
    (r : Equiv.Perm (Fin 4)) : NecessarySafe (fun e => v (entryPerm r e)) :=
  h.reindex (entryPerm r) (entryPerm_complement r)

end Paper2.Certificates.Q6
