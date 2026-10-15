import Paper2.Certificates.Q8MatchingData

/-! The finite candidate indices faithfully encode actual perfect matchings,
including all port coordinates and deleted endpoints. -/
namespace Paper2.Certificates.Q8.Atlas

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem standardMate_injective : Function.Injective standardMate := by
  decide +kernel

theorem fullMate_injective (d : PairIndex) : Function.Injective (fullMate d) := by
  intro k l h
  apply standardMate_injective
  funext i
  have he := congrFun h (residualOrder d i)
  rw [(fullMate_coordinates d k).1 i,(fullMate_coordinates d l).1 i] at he
  have hi := congrArg (residualIndex d) he
  simpa only [(residual_order_valid d).2.1] using hi

/-- Regard a residual perfect matching as an eight-port mate map, fixing the
two deleted endpoints. Fixed endpoints do not create matching edges. -/
def Matching.extend {d : PairIndex} (M : Matching d) (v : Port) : Port :=
  if h : v ≠ (deleted d).1 ∧ v ≠ (deleted d).2 then (M.mate ⟨v,h⟩).val else v

/-- Every actual perfect matching has one unique index with the same full
mate function; the candidate enumeration is not an extra hypothesis. -/
theorem Matching.exists_full_choice {d : PairIndex} (M : Matching d) :
    ∃! k : Choice, M.extend = fullMate d k := by
  obtain ⟨k,hk⟩ := M.exists_choice
  have he : M.extend = fullMate d k := by
    funext v
    by_cases hv : v ≠ (deleted d).1 ∧ v ≠ (deleted d).2
    · let u : Remaining d := ⟨v,hv⟩
      let i := (residualEquiv d).symm u
      have hi : residualOrder d i = v := (residual_order_valid d).2.2 v hv.1 hv.2
      have h := hk i
      have hu : residualEquiv d i = u := (residualEquiv d).apply_symm_apply u
      rw [hu,hi] at h
      rw [Matching.extend,dif_pos hv]
      exact h
    · by_cases hp : v = (deleted d).1
      · subst v
        rw [Matching.extend,dif_neg hv]
        exact (fullMate_coordinates d k).2.1.symm
      · have hq : v = (deleted d).2 := by
          by_contra hq
          exact hv ⟨hp,hq⟩
        subst v
        rw [Matching.extend,dif_neg hv]
        exact (fullMate_coordinates d k).2.2.symm
  refine ⟨k,he,?_⟩
  intro l hl
  exact fullMate_injective d (hl.symm.trans he)

end Paper2.Certificates.Q8.Atlas
