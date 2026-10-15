import Paper2.CommonPhase.ZeroLoops

/-! Same-universe notation for genuine contractions, used only to compare
contraction orders. Every value is the original two-term native-X sum. -/
namespace Paper2.CommonPhase
open EndpointSelfLoop
variable {K : Type*} {ι : Type}

structure PortPair (ι : Type) where
  first : ι
  second : ι
  distinct : first ≠ second

namespace PortPair

def Disjoint (e f : PortPair ι) : Prop :=
  e.first ≠ f.first ∧ e.first ≠ f.second ∧
  e.second ≠ f.first ∧ e.second ≠ f.second

theorem Disjoint.symm {e f : PortPair ι} (h : e.Disjoint f) : f.Disjoint e :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

noncomputable def fill (e : PortPair ι) (x : ι → Bool) (t : Bool) : ι → Bool :=
by
  classical
  exact fun i => if i = e.first then t else if i = e.second then !t else x i

noncomputable def pairSum [AddCommMonoid K] (e : PortPair ι) (f : Tensor K ι) : Tensor K ι :=
  fun x => ∑ t : Bool, f (e.fill x t)

theorem fill_eq_extend (e : PortPair ι) (x : ι → Bool) (t : Bool) :
    e.fill x t = extendPair e.first e.second e.distinct (restrict e.first e.second x) t := by
  classical
  funext i
  by_cases ha : i = e.first
  · simp [fill, extendPair, splitPorts, ha]
  · by_cases hb : i = e.second
    · simp [fill, extendPair, splitPorts, ha, hb, e.distinct.symm, Sum.elim]
    · simp [fill, extendPair, splitPorts, ha, hb, restrict, Sum.elim]

theorem pairSum_eq_loop [AddCommMonoid K] (e : PortPair ι) (f : Tensor K ι) (x : ι → Bool) :
    e.pairSum f x = loop e.first e.second e.distinct f (restrict e.first e.second x) := by
  change (∑ t : Bool, f (e.fill x t)) = ∑ t : Bool,
    f (extendPair e.first e.second e.distinct (restrict e.first e.second x) t)
  simp only [fill_eq_extend]

theorem restrict_extend (e : PortPair ι) (x : Remaining e.first e.second → Bool) (t : Bool) :
    restrict e.first e.second (extendPair e.first e.second e.distinct x t) = x := by
  classical
  funext i
  simp [restrict, extendPair, splitPorts, i.property.1, i.property.2, Sum.elim]
  rfl

theorem fill_comm {e f : PortPair ι} (h : e.Disjoint f) (x : ι → Bool) (s t : Bool) :
    e.fill (f.fill x t) s = f.fill (e.fill x s) t := by
  classical
  funext i
  obtain ⟨hac, had, hbc, hbd⟩ := h
  by_cases ha : i = e.first
  · subst i; simp [fill, hac, had]
  · by_cases hb : i = e.second
    · subst i; simp [fill, e.distinct.symm, hbc, hbd]
    · by_cases hc : i = f.first
      · subst i; simp [fill, ha, hb]
      · by_cases hd : i = f.second
        · subst i; simp [fill, ha, hb, f.distinct.symm]
        · simp [fill, ha, hb, hc, hd]

/-- Actual double native-X contraction is independent of its order. -/
theorem pairSum_comm [AddCommMonoid K] {e f : PortPair ι} (h : e.Disjoint f)
    (F : Tensor K ι) : e.pairSum (f.pairSum F) = f.pairSum (e.pairSum F) := by
  funext x
  simp only [pairSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro s hs
  rw [fill_comm h]

noncomputable def residual (e f : PortPair ι) (h : e.Disjoint f) :
    PortPair (Remaining e.first e.second) where
  first := ⟨f.first, h.1.symm, h.2.2.1.symm⟩
  second := ⟨f.second, h.2.1.symm, h.2.2.2.symm⟩
  distinct := fun he => f.distinct (congrArg Subtype.val he)

theorem restrict_fill (e f : PortPair ι) (h : e.Disjoint f) (x : ι → Bool) (t : Bool) :
    restrict e.first e.second (f.fill x t) =
      (e.residual f h).fill (restrict e.first e.second x) t := by
  classical
  funext i
  simp only [restrict, fill, residual]
  have h₁ : (i = (⟨f.first, h.1.symm, h.2.2.1.symm⟩ : Remaining e.first e.second)) ↔ i.val = f.first := Subtype.ext_iff
  have h₂ : (i = (⟨f.second, h.2.1.symm, h.2.2.2.symm⟩ : Remaining e.first e.second)) ↔ i.val = f.second := Subtype.ext_iff
  simp only [h₁, h₂]

/-- A lifted residual tensor contracts exactly as that residual tensor. -/
theorem pairSum_lift [AddCommMonoid K] (e f : PortPair ι) (h : e.Disjoint f)
    (F : Tensor K (Remaining e.first e.second)) (x : ι → Bool) :
    f.pairSum (fun y => F (restrict e.first e.second y)) x =
      (e.residual f h).pairSum F (restrict e.first e.second x) := by
  simp only [pairSum, restrict_fill e f h]

/-- Any two pairs have a common disjoint pair when at least six ports exist. -/
theorem exists_common_disjoint [Fintype ι] (hn : 6 ≤ Fintype.card ι) (e f : PortPair ι) :
    ∃ g : PortPair ι, e.Disjoint g ∧ f.Disjoint g := by
  classical
  let s : Finset ι := {e.first, e.second, f.first, f.second}
  have hs : s.card ≤ 4 := by
    dsimp [s]
    calc
      _ ≤ ({e.second, f.first, f.second} : Finset ι).card + 1 := Finset.card_insert_le _ _
      _ ≤ 4 := by
        have h₁ := Finset.card_insert_le e.second ({f.first, f.second} : Finset ι)
        have h₂ : ({f.first, f.second} : Finset ι).card ≤ 2 := Finset.card_le_two
        omega
  have hcard : 1 < (Finset.univ \ s).card := by
    have hh := Finset.card_sdiff_add_card_eq_card (show s ⊆ Finset.univ from Finset.subset_univ _)
    simp only [Finset.card_univ] at hh
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  have ha' : a ≠ e.first ∧ a ≠ e.second ∧ a ≠ f.first ∧ a ≠ f.second := by
    simpa [s] using (Finset.mem_sdiff.mp ha).2
  have hb' : b ≠ e.first ∧ b ≠ e.second ∧ b ≠ f.first ∧ b ≠ f.second := by
    simpa [s] using (Finset.mem_sdiff.mp hb).2
  exact ⟨⟨a, b, hab⟩,
    ⟨ha'.1.symm, hb'.1.symm, ha'.2.1.symm, hb'.2.1.symm⟩,
    ⟨ha'.2.2.1.symm, hb'.2.2.1.symm, ha'.2.2.2.symm, hb'.2.2.2.symm⟩⟩

end PortPair
end Paper2.CommonPhase
