import Paper2.HeightOne.Cyclic.MatchingCompletion
import Paper2.HeightOne.Cyclic.LiftWords

/-! Completion of the supported weight-two graph to a perfect matching. The
input matchings are the actual contraction supports, not hypothesized edges. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open EndpointSelfLoop
variable {K : Type*} [Field K]

lemma pairWord_comm {ι : Type} [Fintype ι] (u v : ι) : pairWord u v = pairWord v u := by
  classical
  funext i
  simp only [pairWord, or_comm]

def WeightTwoRel {n : ℕ} (f : Signature K n) (u v : Fin n) : Prop :=
  u ≠ v ∧ f (pairWord u v) ≠ 0

lemma plusCard_pairWord_of_equality {n : ℕ} (f : Signature K n)
    (u v k : Fin n) (huk : u ≠ k) (hvu : v ≠ u) (hvk : v ≠ k)
    (hequal : ∀ x, f x ≠ 0 → x u = x v)
    (p q : Remaining u k) (hpv : p.val ≠ v) (hqv : q.val ≠ v) (s : K) :
    plusContraction u k huk s f (pairWord p q) = f (pairWord p.val q.val) := by
  classical
  rw [plusContraction_apply, extendBits_pairWord]
  have hz : f (extendBits u k huk (pairWord p q) true true) = 0 := by
    by_contra h
    have he := hequal _ h
    have hu : extendBits u k huk (pairWord p q) true true u = true := by
      simp [extendBits, splitPorts]
    have hv : extendBits u k huk (pairWord p q) true true v = false := by
      rw [extendBits_remaining u k huk (pairWord p q) true true ⟨v, hvu, hvk⟩]
      simp only [pairWord, decide_eq_false_iff_not]
      rintro (h | h)
      · exact hpv (congrArg Subtype.val h).symm
      · exact hqv (congrArg Subtype.val h).symm
    rw [hu, hv] at he
    exact Bool.noConfusion he
  rw [hz, mul_zero, sub_zero]

/-- Every original weight-two edge provides the deleted-pair matching data
needed by the purely combinatorial completion lemma. -/
theorem weightTwo_deletion_matchings {n : ℕ} (f : Signature K n) (hf : f ≠ 0)
    (hn : 5 ≤ n) (S : Set K)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ z ∈ S, s ≠ t ∧ s ≠ z ∧ t ≠ z)
    (hcards : ∀ a b (hab : a ≠ b), ∀ q ∈ S, plusContraction a b hab q f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab q f))
    (u v : Fin n) (huv : WeightTwoRel f u v) :
    ∀ k, k ≠ u → k ≠ v → ∃ M : FreeMatching (Remaining u k),
      ∀ p, p.val ≠ v → (M.mate p).val ≠ v → WeightTwoRel f p.val (M.mate p).val := by
  classical
  intro k hku hkv
  have h0 := origin_nonzero_of_matching_cards f hf hn S hthree hcards
  have hequal := weightTwo_forces_equality f hf hn S hthree hcards u v huv.1 huv.2
  obtain ⟨s, hs, t, ht, z, hz, hst, hsz, htz⟩ := hthree
  have hW : f (pairWord u k) = 0 := by
    by_contra h
    have he := weightTwo_unique_partner f hf hn S
      ⟨s, hs, t, ht, z, hz, hst, hsz, htz⟩ hcards u v k huv.1 (Ne.symm hku) huv.2 h
    exact hkv he.symm
  have hcn : plusContraction u k (Ne.symm hku) s f ≠ 0 := by
    intro he
    have hh := congrFun he (fun _ => false)
    rw [plusContraction_apply, extendBits_origin_false, extendBits_origin_true, hW, mul_zero, sub_zero] at hh
    exact h0 hh
  obtain ⟨P, hP⟩ := hcards u k (Ne.symm hku) s hs hcn
  let M := remainingMatching P
  let e := Fintype.equivFin (Remaining u k)
  refine ⟨M, ?_⟩
  intro p hpv hmpv
  have hpm : p ≠ M.mate p := Ne.symm (M.ne p)
  have hed : weightTwoWord (e p) (e (M.mate p)) ∈ equalityCode P := by
    apply (weightTwoWord_mem_iff P _ _ (fun h => hpm (e.injective h))).mpr
    simp [M, e, remainingMatching]
  rw [← hP, mem_support] at hed
  change plusContraction u k (Ne.symm hku) s f (fun i => weightTwoWord (e p) (e (M.mate p)) (e i)) ≠ 0 at hed
  rw [pairWord_pullback] at hed
  simp only [e, Equiv.symm_apply_apply] at hed
  rw [plusCard_pairWord_of_equality f u v k (Ne.symm hku) (Ne.symm huv.1) (Ne.symm hkv) hequal p (M.mate p) hpv hmpv s] at hed
  exact ⟨fun h => hpm (Subtype.ext h), hed⟩

/-- Source cyclic-collapse Step 2's graph conclusion: a nonempty weight-two
graph is perfect, with no omitted ports. -/
theorem weightTwo_is_perfect {n : ℕ} (f : Signature K n) (hf : f ≠ 0)
    (hn : 6 ≤ n) (S : Set K)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ z ∈ S, s ≠ t ∧ s ≠ z ∧ t ≠ z)
    (hcards : ∀ a b (hab : a ≠ b), ∀ q ∈ S, plusContraction a b hab q f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab q f))
    (hedge : ∃ u v, WeightTwoRel f u v) : ∀ x, ∃ y, WeightTwoRel f x y := by
  obtain ⟨u, v, huv⟩ := hedge
  refine matching_relation_is_perfect hn (WeightTwoRel f) ?_ ?_ ?_ u v huv ?_
  · intro a b hab
    exact ⟨Ne.symm hab.1, by rw [pairWord_comm]; exact hab.2⟩
  · intro a haa
    exact haa.1 rfl
  · intro a b c hab hac
    exact weightTwo_unique_partner f hf (by omega) S hthree hcards a b c hab.1 hac.1 hab.2 hac.2
  · exact weightTwo_deletion_matchings f hf (by omega) S hthree hcards u v huv

end
end Paper2.HeightOne.Cyclic
