import Paper2.Certificates.Q6Cards

/-! The twenty-coordinate representation is an exact encoding of the triples
of six labelled ports, rather than an assumption about a preselected support. -/
namespace Paper2.Certificates.Q6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask_injective : Function.Injective mask := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tripleMasks_injective : Function.Injective tripleMasks := by
  decide +kernel

def tripleSet (i : Fin 20) : PortSet :=
  Finset.univ.filter (fun v => (tripleMasks i).testBit v.val = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tripleSet_correct (i : Fin 20) :
    (tripleSet i).card = 3 ∧ mask (tripleSet i) = tripleMasks i := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tripleMasks_complete (S : PortSet) (hS : S.card = 3) :
    ∃ i : Fin 20, mask S = tripleMasks i := by
  revert S
  decide +kernel

noncomputable def tripleEquiv : Fin 20 ≃ {S : PortSet // S.card = 3} :=
  Equiv.ofBijective (fun i => ⟨tripleSet i, (tripleSet_correct i).1⟩) (by
    constructor
    · intro i j hij
      apply tripleMasks_injective
      have hm := congrArg (fun S : {S : PortSet // S.card = 3} => mask S.val) hij
      simpa only [(tripleSet_correct i).2, (tripleSet_correct j).2] using hm
    · rintro ⟨S, hS⟩
      obtain ⟨i, hi⟩ := tripleMasks_complete S hS
      refine ⟨i, Subtype.ext ?_⟩
      apply mask_injective
      exact (tripleSet_correct i).2.trans hi.symm)

theorem coefficient_at_triple {K : Type*} [Zero K] (q : Fin 20 → K) (i : Fin 20) :
    coefficient q (tripleMasks i) = q i := by
  fin_cases i <;> rfl

end Paper2.Certificates.Q6
