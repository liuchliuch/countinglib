import Paper2.Certificates.Q8Atlas

/-! Port relabeling of the literal deletion-and-splice atlas. This transports
actual residual matching objects, including the normalized root condition. -/
namespace Paper2.Certificates.Q8.Atlas

structure Relabeling where
  ports : Equiv.Perm Port
  pairs : Equiv.Perm PairIndex
  endpoints : ∀ d,
    (ports (deleted d).1 = (deleted (pairs d)).1 ∧
      ports (deleted d).2 = (deleted (pairs d)).2) ∨
    (ports (deleted d).1 = (deleted (pairs d)).2 ∧
      ports (deleted d).2 = (deleted (pairs d)).1)

theorem Relabeling.remaining_iff (r : Relabeling) (d : PairIndex) (v : Port) :
    (r.ports v ≠ (deleted (r.pairs d)).1 ∧ r.ports v ≠ (deleted (r.pairs d)).2) ↔
      (v ≠ (deleted d).1 ∧ v ≠ (deleted d).2) := by
  rcases r.endpoints d with h | h
  · rw [←h.1,←h.2]
    simp only [ne_eq,Equiv.apply_eq_iff_eq]
  · rw [←h.1,←h.2]
    simp only [ne_eq,Equiv.apply_eq_iff_eq, and_comm]

def Relabeling.remainingEquiv (r : Relabeling) (d : PairIndex) :
    Remaining d ≃ Remaining (r.pairs d) where
  toFun v := ⟨r.ports v.val,(r.remaining_iff d v.val).mpr v.property⟩
  invFun v := ⟨r.ports.symm v.val,(r.remaining_iff d _).mp (by
    simpa only [r.ports.apply_symm_apply] using v.property)⟩
  left_inv v := Subtype.ext (r.ports.symm_apply_apply v.val)
  right_inv v := Subtype.ext (r.ports.apply_symm_apply v.val)

def Relabeling.family (r : Relabeling) (M : (d : PairIndex) → Matching d)
    (d : PairIndex) : Matching d where
  mate v := (r.remainingEquiv d).symm ((M (r.pairs d)).mate (r.remainingEquiv d v))
  involutive v := by
    simp only [(r.remainingEquiv d).apply_symm_apply]
    rw [(M (r.pairs d)).involutive]
    exact (r.remainingEquiv d).symm_apply_apply v
  no_fixed v := by
    intro h
    have hh := congrArg (r.remainingEquiv d) h
    simp only [(r.remainingEquiv d).apply_symm_apply] at hh
    exact (M (r.pairs d)).no_fixed _ hh

theorem Relabeling.extend_family (r : Relabeling) (M : (d : PairIndex) → Matching d)
    (d : PairIndex) (v : Port) :
    (r.family M d).extend v = r.ports.symm ((M (r.pairs d)).extend (r.ports v)) := by
  by_cases h : v ≠ (deleted d).1 ∧ v ≠ (deleted d).2
  · have h' := (r.remaining_iff d v).mpr h
    simp only [Matching.extend,dif_pos h,dif_pos h']
    rfl
  · have h' : ¬(r.ports v ≠ (deleted (r.pairs d)).1 ∧
        r.ports v ≠ (deleted (r.pairs d)).2) := fun hh => h ((r.remaining_iff d v).mp hh)
    simp only [Matching.extend,dif_neg h,dif_neg h',r.ports.symm_apply_apply]

def spliceAt (m : Port → Port) (a b v : Port) : Port :=
  if v = a ∨ v = b then v
  else if m v = a then m b else if m v = b then m a else m v

theorem spliceAt_swap (m : Port → Port) (a b v : Port) (hab : a ≠ b) :
    spliceAt m a b v = spliceAt m b a v := by
  by_cases hv : v = a ∨ v = b
  · simp only [spliceAt,hv,or_comm,ite_true]
  · have hv' : ¬(v = b ∨ v = a) := by simpa only [or_comm] using hv
    by_cases ha : m v = a
    · have hb : m v ≠ b := by simpa only [ha] using hab
      simp only [spliceAt,if_neg hv,if_neg hv',if_pos ha,if_neg hb]
    · by_cases hb : m v = b <;>
        simp only [spliceAt,if_neg hv,if_neg hv',if_neg ha,hb,ite_true,ite_false,Ne.symm hab]

theorem spliceAt_conjugate (p : Equiv.Perm Port) (m : Port → Port) (a b v : Port) :
    p (spliceAt (fun w => p.symm (m (p w))) a b v) =
      spliceAt m (p a) (p b) (p v) := by
  have ha : (p.symm (m (p v)) = a) ↔ (m (p v) = p a) :=
    p.symm_apply_eq
  have hb : (p.symm (m (p v)) = b) ↔ (m (p v) = p b) :=
    p.symm_apply_eq
  simp only [spliceAt,ne_eq,Equiv.apply_eq_iff_eq,ha,hb]
  split_ifs <;> simp only [p.apply_symm_apply]

theorem deleted_distinct (d : PairIndex) : (deleted d).1 ≠ (deleted d).2 := by
  revert d
  decide +kernel

theorem Relabeling.splice_family (r : Relabeling) (M : (d : PairIndex) → Matching d)
    (d e : PairIndex) (v : Port) :
    r.ports (spliceMate (r.family M d).extend e v) =
      spliceMate (M (r.pairs d)).extend (r.pairs e) (r.ports v) := by
  have hext : (r.family M d).extend =
      fun w => r.ports.symm ((M (r.pairs d)).extend (r.ports w)) :=
    funext (r.extend_family M d)
  rw [hext]
  change r.ports (spliceAt (fun w => r.ports.symm ((M (r.pairs d)).extend (r.ports w)))
    (deleted e).1 (deleted e).2 v) =
    spliceAt (M (r.pairs d)).extend (deleted (r.pairs e)).1 (deleted (r.pairs e)).2 (r.ports v)
  rw [spliceAt_conjugate]
  rcases r.endpoints e with h | h
  · rw [h.1,h.2]
  · rw [h.1,h.2]
    exact spliceAt_swap _ _ _ _ (Ne.symm (deleted_distinct _))

theorem Relabeling.disjoint_iff (r : Relabeling) (d e : PairIndex) :
    DisjointDeleted (r.pairs d) (r.pairs e) ↔ DisjointDeleted d e := by
  rcases r.endpoints d with hd | hd <;> rcases r.endpoints e with he | he <;>
    simp only [DisjointDeleted,←hd.1,←hd.2,←he.1,←he.2,
      ne_eq,Equiv.apply_eq_iff_eq,and_assoc,and_left_comm,and_comm]

theorem MatchingFamilyCompatible.relabel {M : (d : PairIndex) → Matching d}
    (h : MatchingFamilyCompatible M) (r : Relabeling) : MatchingFamilyCompatible (r.family M) := by
  intro d e hde
  funext v
  apply r.ports.injective
  rw [r.splice_family,r.splice_family]
  exact congrFun (h _ _ ((r.disjoint_iff d e).mpr hde)) (r.ports v)

theorem MatchingFamilyCollisionFree.relabel {M : (d : PairIndex) → Matching d}
    (h : MatchingFamilyCollisionFree M) (r : Relabeling) : MatchingFamilyCollisionFree (r.family M) := by
  intro d e hne hmeet hedge
  apply h (r.pairs d) (r.pairs e) (fun hh => hne (r.pairs.injective hh))
    (fun hh => hmeet ((r.disjoint_iff d e).mp hh))
  obtain ⟨u,v,huv,hd,he⟩ := hedge
  refine ⟨r.ports u,r.ports v,fun hh => huv (r.ports.injective hh),?_,?_⟩
  · have hh := congrArg r.ports hd
    rw [r.extend_family,r.ports.apply_symm_apply] at hh
    exact hh
  · have hh := congrArg r.ports he
    rw [r.extend_family,r.ports.apply_symm_apply] at hh
    exact hh

end Paper2.Certificates.Q8.Atlas
