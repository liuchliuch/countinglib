import Counting.Algorithm.KarpLuby.Program
import Counting.Algorithm.KarpLuby.Estimator
import Counting.Algorithm.KarpLuby.DNFCover

/-!
# Correctness of executable prefix selection

The selected integer interval and clause unranking give an explicit inverse for
every tagged satisfying assignment. This connects the implementation to finite
cover analysis without enumerating the assignment space in the program.
-/
namespace Counting.Algorithm.KarpLuby.Program

open DNF
variable {n : ℕ}

/-- The exact prefix offset and free-variable rank of every selected assignment. -/
theorem select_some_iff (cs : List (Clause n)) (r i : ℕ) (a : Assignment n) :
    select cs r = some (i, a) ↔
      ∃ hi : i < cs.length, Satisfies cs[i] a ∧
        r = totalMass (cs.take i) + rankNat cs[i] a := by
  induction cs generalizing r i with
  | nil => simp [select]
  | cons c cs ih =>
    cases i with
    | zero =>
      simp only [List.length_cons, Nat.zero_lt_succ, List.getElem_cons_zero,
        List.take_zero, totalMass_nil, zero_add, exists_true_left]
      by_cases hr : r < clauseMass c
      · simp only [select, hr, ↓reduceIte]
        constructor
        · intro h
          have ha : sampleNat c r = a := congrArg Prod.snd (Option.some.inj h)
          rw [← ha]
          exact ⟨sampleNat_satisfies c r, (rankNat_sampleNat c r hr).symm⟩
        · rintro ⟨ha, he⟩
          rw [he, sampleNat_rankNat c a ha]
      · simp only [select, hr, ↓reduceIte]
        constructor
        · intro h
          obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp h
          have := congrArg Prod.fst hp
          simp at this
        · rintro ⟨_, he⟩
          exact (hr (he ▸ rankNat_lt c a)).elim
    | succ i =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff, List.getElem_cons_succ,
        List.take_succ_cons, totalMass_cons]
      by_cases hr : r < clauseMass c
      · simp only [select, hr, ↓reduceIte]
        constructor
        · intro h
          have := congrArg Prod.fst (Option.some.inj h)
          simp at this
        · rintro ⟨hi, _, he⟩
          omega
      · simp only [select, hr, ↓reduceIte]
        constructor
        · intro h
          obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
          have hpi : p.1 = i := by have := congrArg Prod.fst he; omega
          have hpa : p.2 = a := congrArg Prod.snd he
          have hp' : p = (i, a) := Prod.ext hpi hpa
          rw [hp'] at hp
          obtain ⟨hi, ha, heq⟩ := (ih (r - clauseMass c) i).mp hp
          exact ⟨hi, ha, by omega⟩
        · rintro ⟨hi, ha, he⟩
          have hsel : select cs (r - clauseMass c) = some (i, a) :=
            (ih (r - clauseMass c) i).mpr ⟨hi, ha, by omega⟩
          simp [hsel]

/-- Every successful selection lies in its selected clause. -/
theorem select_sound (cs : List (Clause n)) (r i : ℕ) (a : Assignment n)
    (h : select cs r = some (i, a)) :
    ∃ hi : i < cs.length, Satisfies cs[i] a := by
  obtain ⟨hi, ha, _⟩ := (select_some_iff cs r i a).mp h
  exact ⟨hi, ha⟩

/-- Distinct valid integer ranks never select the same tagged assignment. -/
theorem select_injective (cs : List (Clause n)) {r s i : ℕ} {a : Assignment n}
    (hr : select cs r = some (i, a)) (hs : select cs s = some (i, a)) : r = s := by
  obtain ⟨_, _, he₁⟩ := (select_some_iff cs r i a).mp hr
  obtain ⟨_, _, he₂⟩ := (select_some_iff cs s i a).mp hs
  exact he₁.trans he₂.symm

/-- Prefix sums and the clause rank recover every tagged satisfying assignment. -/
theorem select_prefix_rank (cs : List (Clause n)) (i : Fin cs.length)
    (a : Assignment n) (ha : Satisfies cs[i.val] a) :
    select cs (totalMass (cs.take i.val) + rankNat cs[i.val] a) = some (i.val, a) :=
  (select_some_iff cs _ i.val a).mpr ⟨i.isLt, ha, rfl⟩

/-- Reading a valid rank always returns a pair, without a default element. -/
def selectedPair (cs : List (Clause n)) (r : Fin (totalMass cs)) : ℕ × Assignment n :=
  (select cs r.val).get (Option.isSome_iff_ne_none.mpr (by
    intro h
    have := (select_eq_none_iff cs r.val).mp h
    omega))

theorem select_selectedPair (cs : List (Clause n)) (r : Fin (totalMass cs)) :
    select cs r.val = some (selectedPair cs r) := by
  exact (Option.some_get _).symm

/-- Executable unranking into the semantic tagged union. -/
def unrankTagged (cs : List (Clause n)) (r : Fin (totalMass cs)) :
    {p // p ∈ tagged (clauseFamily cs)} := by
  let p := selectedPair cs r
  have hp := select_sound cs r.val p.1 p.2 (select_selectedPair cs r)
  have hi : p.1 < cs.length := by obtain ⟨h, _⟩ := hp; exact h
  have ha : Satisfies cs[p.1] p.2 := by obtain ⟨_, h⟩ := hp; exact h
  exact ⟨⟨⟨p.1, hi⟩, p.2⟩, by simpa using ha⟩

theorem select_unrankTagged (cs : List (Clause n)) (r : Fin (totalMass cs)) :
    select cs r.val = some ((unrankTagged cs r).val.1.val, (unrankTagged cs r).val.2) :=
  select_selectedPair cs r

/-- The prefix rank is within the total mass because selection succeeds there. -/
theorem prefix_rank_lt (cs : List (Clause n)) (i : Fin cs.length)
    (a : Assignment n) (ha : Satisfies cs[i.val] a) :
    totalMass (cs.take i.val) + rankNat cs[i.val] a < totalMass cs := by
  by_contra h
  have hn := (select_eq_none_iff cs _).mpr (Nat.le_of_not_gt h)
  rw [select_prefix_rank cs i a ha] at hn
  cases hn

/-- Explicit inverse: the mass of preceding clauses plus the clause-local rank. -/
def rankTagged (cs : List (Clause n)) (p : {p // p ∈ tagged (clauseFamily cs)}) :
    Fin (totalMass cs) :=
  ⟨totalMass (cs.take p.val.1.val) + rankNat cs[p.val.1.val] p.val.2,
    prefix_rank_lt cs p.val.1 p.val.2 ((mem_clauseFamily cs p.val.1 p.val.2).mp
      ((mem_tagged (clauseFamily cs) p.val).mp p.property))⟩

theorem select_rankTagged (cs : List (Clause n)) (p : {p // p ∈ tagged (clauseFamily cs)}) :
    select cs (rankTagged cs p).val = some (p.val.1.val, p.val.2) :=
  select_prefix_rank cs p.val.1 p.val.2 ((mem_clauseFamily cs p.val.1 p.val.2).mp
      ((mem_tagged (clauseFamily cs) p.val).mp p.property))

/-- Prefix selection and clause ranks are inverse, including duplicate clauses. -/
def taggedEquiv (cs : List (Clause n)) :
    Fin (totalMass cs) ≃ {p // p ∈ tagged (clauseFamily cs)} where
  toFun := unrankTagged cs
  invFun := rankTagged cs
  left_inv r := by
    apply Fin.ext
    exact select_injective cs (select_rankTagged cs (unrankTagged cs r))
      (select_unrankTagged cs r)
  right_inv p := by
    have h := Option.some.inj ((select_unrankTagged cs (rankTagged cs p)).symm.trans
      (select_rankTagged cs p))
    apply Subtype.ext
    apply Sigma.ext (Fin.ext (congrArg Prod.fst h))
    exact heq_of_eq (congrArg Prod.snd h)

@[simp] theorem mass_clauseFamily_eq_totalMass (cs : List (Clause n)) :
    mass (clauseFamily cs) = totalMass cs := mass_clauseFamily cs

/-- The semantic ranking is the executable prefix/clause inverse. -/
def clauseRanking (cs : List (Clause n)) :
    {p // p ∈ tagged (clauseFamily cs)} ≃ Fin (mass (clauseFamily cs)) :=
  (taggedEquiv cs).symm.trans (finCongr (mass_clauseFamily_eq_totalMass cs).symm)

/-- The executable prefix scan is exactly the least-occurrence owner predicate. -/
theorem owner_eq_true_iff (cs : List (Clause n)) (i : Fin cs.length) (a : Assignment n) :
    owner cs i.val a = true ↔ IsOwner (clauseFamily cs) ⟨i, a⟩ := by
  have ho : owner cs i.val a = true ↔
      ∀ c, c ∈ cs.take i.val → ¬ Satisfies c a := by
    simp [owner]
  rw [ho]
  constructor
  · intro h j hj
    rw [mem_clauseFamily]
    apply h (cs.get j)
    have hji : j.val < (cs.take i.val).length := by
      simp only [List.length_take]
      exact Nat.lt_min.mpr ⟨hj, j.isLt⟩
    exact List.mem_iff_getElem.mpr ⟨j.val, hji, by simp⟩
  · intro h c hc
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hc
    have hjl : j < cs.length := lt_of_lt_of_le hj (List.length_take_le' _ _)
    have hji : (⟨j, hjl⟩ : Fin cs.length) < i :=
      show j < i.val from lt_of_lt_of_le hj (List.length_take_le _ _)
    have he' : cs.get ⟨j, hjl⟩ = c := by simpa using he
    rw [← he']
    simpa using h ⟨j, hjl⟩ hji

theorem clauseRanking_symm_apply (cs : List (Clause n)) (r : Fin (mass (clauseFamily cs))) :
    (clauseRanking cs).symm r =
      unrankTagged cs ⟨r.val, by simpa only [mass_clauseFamily_eq_totalMass] using r.isLt⟩ := rfl

/-- A valid prefix selection agrees with the owner-filtered finite-cover trial. -/
theorem trial_lt_mass (cs : List (Clause n)) (r : ℕ) (hr : r < totalMass cs) :
    (trial cs r : ℚ) =
      if IsOwner (clauseFamily cs) (unrankTagged cs ⟨r, hr⟩).val
      then (dyadicSize (totalMass cs) : ℚ) else 0 := by
  unfold trial
  rw [select_unrankTagged cs ⟨r, hr⟩]
  simp only [owner_eq_true_iff, Nat.cast_ite, Nat.cast_zero]

/-- Transport only the length proof; integer codes are unchanged. -/
def dyadicRankEquiv (cs : List (Clause n)) :
    Fin (dyadicSize (totalMass cs)) ≃ Fin (dyadicSize (mass (clauseFamily cs))) :=
  finCongr (congrArg dyadicSize (mass_clauseFamily_eq_totalMass cs).symm)

/-- Pointwise refinement of the executable trial by the ranked estimator. -/
theorem trial_eq_rankedTrial (cs : List (Clause n)) (r : Fin (dyadicSize (totalMass cs))) :
    (trial cs r.val : ℚ) =
      rankedTrial (clauseFamily cs) (clauseRanking cs) (dyadicRankEquiv cs r) := by
  unfold rankedTrial
  change (trial cs r.val : ℚ) =
    if h : r.val < mass (clauseFamily cs) then
      if IsOwner (clauseFamily cs) ((clauseRanking cs).symm ⟨r.val, h⟩).val
      then (dyadicSize (mass (clauseFamily cs)) : ℚ) else 0
    else 0
  by_cases hr : r.val < mass (clauseFamily cs)
  · simp only [hr, ↓reduceDIte]
    rw [clauseRanking_symm_apply]
    simpa only [mass_clauseFamily_eq_totalMass] using
      trial_lt_mass cs r.val (by simpa only [mass_clauseFamily_eq_totalMass] using hr)
  · simp only [hr, ↓reduceDIte]
    rw [trial_of_mass_le cs r.val (by
      simpa only [mass_clauseFamily_eq_totalMass] using Nat.le_of_not_gt hr)]
    rfl

open HiddenCircuits.Approximation.SelfReduction

/-- The actual executable padded trial is unbiased for the normalized cover count. -/
theorem mean_trial (cs : List (Clause n)) :
    mean (fun r : Fin (dyadicSize (totalMass cs)) => (trial cs r.val : ℚ)) =
      (count (clauseFamily cs) : ℚ) := by
  calc
    _ = mean (fun r => rankedTrial (clauseFamily cs) (clauseRanking cs)
        (dyadicRankEquiv cs r)) := mean_congr (trial_eq_rankedTrial cs)
    _ = mean (rankedTrial (clauseFamily cs) (clauseRanking cs)) :=
      mean_equiv (dyadicRankEquiv cs) (rankedTrial (clauseFamily cs) (clauseRanking cs))
    _ = mean (coverTrial (clauseFamily cs) (clauseRanking cs)) :=
      (mean_decodeTape _ _).symm
    _ = _ := mean_coverTrial _ _

/-- The implementation inherits the exact padded second moment. -/
theorem secondMoment_trial (cs : List (Clause n)) :
    mean (fun r : Fin (dyadicSize (totalMass cs)) => (trial cs r.val : ℚ)^2) =
      (dyadicSize (totalMass cs) : ℚ) * count (clauseFamily cs) := by
  calc
    _ = mean (fun r => rankedTrial (clauseFamily cs) (clauseRanking cs)
        (dyadicRankEquiv cs r)^2) :=
      mean_congr (fun r => congrArg (fun x : ℚ => x^2) (trial_eq_rankedTrial cs r))
    _ = mean (fun r => rankedTrial (clauseFamily cs) (clauseRanking cs) r ^2) :=
      mean_equiv (dyadicRankEquiv cs)
        (fun r => rankedTrial (clauseFamily cs) (clauseRanking cs) r ^ 2)
    _ = mean (fun t => coverTrial (clauseFamily cs) (clauseRanking cs) t ^2) :=
      (mean_decodeTape (dyadicBits (mass (clauseFamily cs)))
        (fun r => rankedTrial (clauseFamily cs) (clauseRanking cs) r ^ 2)).symm
    _ = _ := by
      simpa only [mass_clauseFamily_eq_totalMass] using
        secondMoment_coverTrial (clauseFamily cs) (clauseRanking cs)

/-- Overlap and dyadic padding cost at most a factor twice the clause count. -/
theorem secondMoment_trial_le (cs : List (Clause n)) :
    mean (fun r : Fin (dyadicSize (totalMass cs)) => (trial cs r.val : ℚ)^2) ≤
      2 * (cs.length : ℚ) * (count (clauseFamily cs) : ℚ)^2 := by
  rw [secondMoment_trial]
  simpa only [secondMoment_coverTrial, mass_clauseFamily_eq_totalMass] using
    secondMoment_coverTrial_le (clauseFamily cs) (clauseRanking cs)

/-- Zero-count inputs return zero for every code, including padded codes. -/
theorem trial_of_count_zero (cs : List (Clause n)) (hc : count (clauseFamily cs) = 0)
    (r : ℕ) : trial cs r = 0 := by
  apply trial_of_zero_mass cs _ r
  rw [← mass_clauseFamily_eq_totalMass]
  exact (count_eq_zero_iff_mass_eq_zero _).mp hc

end Counting.Algorithm.KarpLuby.Program
