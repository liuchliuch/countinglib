import Paper2.Certificates.Q8AtlasNormalization

/-! The initial normalized 01-card hypothesis is discharged by actual port
relabeling; the conclusion applies to every compatible residual-matching deck. -/
namespace Paper2.Certificates.Q8.Atlas

theorem port_xor_comm (p q : Port) : Fin.xor p q = Fin.xor q p := by
  revert p q
  decide +kernel

theorem Relabeling.translation_of_family (r : Relabeling)
    (M : (d : PairIndex) → Matching d)
    (h : ∃ p : Equiv.Perm Port, ∀ d v, v ≠ (deleted d).1 → v ≠ (deleted d).2 →
      p ((r.family M d).extend v) = Fin.xor (p v) (Fin.xor (p (deleted d).1) (p (deleted d).2))) :
    ∃ p : Equiv.Perm Port, ∀ d v, v ≠ (deleted d).1 → v ≠ (deleted d).2 →
      p ((M d).extend v) = Fin.xor (p v) (Fin.xor (p (deleted d).1) (p (deleted d).2)) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨r.ports.symm.trans p,?_⟩
  intro d v hleft hright
  have hv : r.ports.symm v ≠ (deleted (r.pairs.symm d)).1 ∧
      r.ports.symm v ≠ (deleted (r.pairs.symm d)).2 := by
    apply (r.remaining_iff (r.pairs.symm d) (r.ports.symm v)).mp
    simpa only [r.ports.apply_symm_apply,r.pairs.apply_symm_apply] using And.intro hleft hright
  have hh := hp (r.pairs.symm d) (r.ports.symm v) hv.1 hv.2
  rw [r.extend_family,r.ports.apply_symm_apply,r.pairs.apply_symm_apply] at hh
  change p (r.ports.symm ((M d).extend v)) =
    Fin.xor (p (r.ports.symm v))
      (Fin.xor (p (r.ports.symm (deleted d).1)) (p (r.ports.symm (deleted d).2)))
  rcases r.endpoints (r.pairs.symm d) with he | he
  · have h1 := congrArg r.ports.symm he.1
    have h2 := congrArg r.ports.symm he.2
    simp only [r.ports.symm_apply_apply,r.pairs.apply_symm_apply] at h1 h2
    rw [←h1,←h2]
    exact hh
  · have h1 := congrArg r.ports.symm he.1
    have h2 := congrArg r.ports.symm he.2
    simp only [r.ports.symm_apply_apply,r.pairs.apply_symm_apply] at h1 h2
    rw [←h1,←h2,port_xor_comm (p (deleted (r.pairs.symm d)).2)]
    exact hh

/-- Source A.9: every collision-free compatible atlas has genuine F₂³ labels,
with no choice of the initial residual matching assumed. -/
theorem collision_free_translation (M : (d : PairIndex) → Matching d)
    (h : MatchingFamilyCompatible M) (hc : MatchingFamilyCollisionFree M) :
    ∃ p : Equiv.Perm Port, ∀ d v, v ≠ (deleted d).1 → v ≠ (deleted d).2 →
      p ((M d).extend v) = Fin.xor (p v) (Fin.xor (p (deleted d).1) (p (deleted d).2)) := by
  obtain ⟨k,hk,_⟩ := (M 0).exists_full_choice
  let r := normalization k
  apply r.translation_of_family M
  exact actual_collision_free_translation (r.family M) (h.relabel r)
    (normalization_family_root M k hk) (hc.relabel r)

end Paper2.Certificates.Q8.Atlas
