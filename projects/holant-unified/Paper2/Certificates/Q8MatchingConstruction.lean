import Paper2.Certificates.Q8MatchingSemantics

namespace Paper2.Certificates.Q8.Atlas

/-- Every enumerated candidate is itself a genuine residual perfect matching. -/
def Matching.ofChoice (d : PairIndex) (k : Choice) : Matching d where
  mate v := residualEquiv d (standardMate k ((residualEquiv d).symm v))
  involutive v := by
    simp only [(residualEquiv d).symm_apply_apply]
    rw [(standardMate_valid k).1 ((residualEquiv d).symm v)]
    exact (residualEquiv d).apply_symm_apply v
  no_fixed v := by
    intro h
    have he := congrArg (residualEquiv d).symm h
    simp only [(residualEquiv d).symm_apply_apply] at he
    exact (standardMate_valid k).2 _ he

theorem Matching.extend_residual {d : PairIndex} (M : Matching d) (i : Fin 6) :
    M.extend (residualOrder d i) = (M.mate (residualEquiv d i)).val := by
  unfold Matching.extend
  rw [dif_pos ((residual_order_valid d).1 i)]
  rfl

theorem Matching.ofChoice_extend (d : PairIndex) (k : Choice) :
    (Matching.ofChoice d k).extend = fullMate d k := by
  obtain ⟨l,hl,_⟩ := (Matching.ofChoice d k).exists_full_choice
  have hkl : k = l := by
    apply standardMate_injective
    funext i
    have he := congrFun hl (residualOrder d i)
    rw [Matching.extend_residual,(fullMate_coordinates d l).1 i] at he
    change (residualEquiv d (standardMate k ((residualEquiv d).symm (residualEquiv d i)))).val = _ at he
    rw [(residualEquiv d).symm_apply_apply] at he
    have hh := congrArg (residualIndex d) he
    change residualIndex d (residualOrder d (standardMate k i)) =
      residualIndex d (residualOrder d (standardMate l i)) at hh
    simpa only [(residual_order_valid d).2.1] using hh
  simpa only [hkl] using hl

end Paper2.Certificates.Q8.Atlas
