import Paper2.HeightOne.Parity
import Paper2.Matching

/-! The linear-support mechanism in source Lemma 5.19: three nonzero affine
pencil members with equally sized xor-linear supports must have one support.
Zero members are handled by actual proportionality, including N=3. -/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open scoped BigOperators
variable {K : Type*} [Field K] {ι : Type} [Fintype ι]

abbrev Word (ι : Type) := ι → Bool

def xorWord (x y : Word ι) : Word ι := fun i => Bool.xor (x i) (y i)

def XorClosed (S : Finset (Word ι)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, xorWord x y ∈ S

lemma xorWord_cancel_right (x y : Word ι) : xorWord (xorWord x y) y = x := by
  funext i
  simp only [xorWord]
  cases x i <;> cases y i <;> rfl

lemma xorWord_cancel_left (x y : Word ι) : xorWord (xorWord x y) x = y := by
  funext i
  simp only [xorWord]
  cases x i <;> cases y i <;> rfl

/-- A xor-linear support cannot be covered by two proper xor-linear subspaces.
Unlike the affine-coset statement this is valid over the two-element field. -/
lemma xorClosed_subset_union {S U V : Finset (Word ι)}
    (hS : XorClosed S) (hU : XorClosed U) (hV : XorClosed V)
    (h : S ⊆ U ∪ V) : S ⊆ U ∨ S ⊆ V := by
  classical
  by_cases hu : S ⊆ U
  · exact Or.inl hu
  by_cases hv : S ⊆ V
  · exact Or.inr hv
  obtain ⟨x, hx, hxu⟩ := Finset.not_subset.mp hu
  obtain ⟨y, hy, hyv⟩ := Finset.not_subset.mp hv
  have hxv : x ∈ V := (Finset.mem_union.mp (h hx)).resolve_left hxu
  have hyu : y ∈ U := (Finset.mem_union.mp (h hy)).resolve_right hyv
  have hxy := hS x hx y hy
  rcases Finset.mem_union.mp (h hxy) with hxyu | hxyv
  · exact False.elim (hxu (xorWord_cancel_right x y ▸ hU _ hxyu _ hyu))
  · exact False.elim (hyv (xorWord_cancel_left x y ▸ hV _ hxyv _ hxv))

def support (f : Word ι → K) : Finset (Word ι) := by
  classical
  exact Finset.univ.filter (fun x => f x ≠ 0)

@[simp] lemma mem_support (f : Word ι → K) (x : Word ι) : x ∈ support f ↔ f x ≠ 0 := by
  classical
  simp [support]

def pencil (A B : Word ι → K) (s : K) : Word ι → K := fun x => A x - s * B x

lemma pencil_support_union (A B : Word ι → K) {s t : K} (hst : s ≠ t) :
    support (pencil A B s) ∪ support (pencil A B t) = support A ∪ support B := by
  classical
  ext x
  simp only [Finset.mem_union, mem_support, pencil]
  constructor
  · rintro (hs | ht) <;> by_contra h <;> push Not at h
    · exact hs (by simp [h.1, h.2])
    · exact ht (by simp [h.1, h.2])
  · exact affine_survives_one_of_two hst

lemma pencil_zero_support (A B : Word ι → K) {z s : K}
    (hz : pencil A B z = 0) (hs : s ≠ z) : support (pencil A B s) = support B := by
  classical
  ext x
  have he : A x = z * B x := sub_eq_zero.mp (congrFun hz x)
  have hp : pencil A B s x = (z - s) * B x := by simp only [pencil, he]; ring
  simp only [mem_support, hp, mul_ne_zero_iff]
  exact and_iff_right (sub_ne_zero.mpr hs.symm)

lemma three_pencil_supports_equal (A B : Word ι → K) {s t u : K}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hs : XorClosed (support (pencil A B s)))
    (ht : XorClosed (support (pencil A B t)))
    (hu : XorClosed (support (pencil A B u)))
    (hcardST : (support (pencil A B s)).card = (support (pencil A B t)).card)
    (hcardSU : (support (pencil A B s)).card = (support (pencil A B u)).card) :
    support (pencil A B s) = support (pencil A B t) := by
  have hsub : support (pencil A B u) ⊆ support (pencil A B s) ∪ support (pencil A B t) := by
    rw [pencil_support_union A B hst, ← pencil_support_union A B hsu]
    exact Finset.subset_union_right
  rcases xorClosed_subset_union hu hs ht hsub with hus | hut
  · have heus : support (pencil A B u) = support (pencil A B s) :=
      Finset.eq_of_subset_of_card_le hus hcardSU.le
    have heunion := (pencil_support_union A B hst).trans (pencil_support_union A B hsu).symm
    rw [heus, Finset.union_self] at heunion
    have hts : support (pencil A B t) ⊆ support (pencil A B s) := by
      rw [← heunion]
      exact Finset.subset_union_right
    exact (Finset.eq_of_subset_of_card_le hts hcardST.le).symm
  · have heut : support (pencil A B u) = support (pencil A B t) :=
      Finset.eq_of_subset_of_card_le hut (by omega)
    have heunion := (pencil_support_union A B hst).trans (pencil_support_union A B htu).symm
    rw [heut, Finset.union_self] at heunion
    have hst' : support (pencil A B s) ⊆ support (pencil A B t) := by
      rw [← heunion]
      exact Finset.subset_union_left
    exact Finset.eq_of_subset_of_card_le hst' hcardST.symm.le

/-- Every nonzero member on a three-or-more-point phase set has the same linear
support. Each member may initially have a different matching. -/
theorem pencil_support_constant (A B : Word ι → K) (S : Set K)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ u ∈ S, s ≠ t ∧ s ≠ u ∧ t ≠ u)
    (hlinear : ∀ s ∈ S, pencil A B s ≠ 0 → XorClosed (support (pencil A B s)))
    (k : ℕ) (hcard : ∀ s ∈ S, pencil A B s ≠ 0 → (support (pencil A B s)).card = k) :
    ∀ s ∈ S, ∀ t ∈ S, pencil A B s ≠ 0 → pencil A B t ≠ 0 →
      support (pencil A B s) = support (pencil A B t) := by
  classical
  by_cases hz : ∃ z ∈ S, pencil A B z = 0
  · obtain ⟨z, hzS, hz⟩ := hz
    intro s hs t ht hsn htn
    have hs' : s ≠ z := by rintro rfl; exact hsn hz
    have ht' : t ≠ z := by rintro rfl; exact htn hz
    rw [pencil_zero_support A B hz hs', pencil_zero_support A B hz ht']
  · have hn : ∀ s ∈ S, pencil A B s ≠ 0 := fun s hs h => hz ⟨s, hs, h⟩
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hthree
    have heab := three_pencil_supports_equal A B hab hac hbc
      (hlinear a ha (hn a ha)) (hlinear b hb (hn b hb)) (hlinear c hc (hn c hc))
      ((hcard a ha (hn a ha)).trans (hcard b hb (hn b hb)).symm)
      ((hcard a ha (hn a ha)).trans (hcard c hc (hn c hc)).symm)
    have hall : ∀ s ∈ S, support (pencil A B s) = support (pencil A B a) := by
      intro s hs
      by_cases hsa : s = a
      · rw [hsa]
      by_cases hsb : s = b
      · rw [hsb, heab]
      have hsub : support (pencil A B s) ⊆ support (pencil A B a) := by
        have h := (pencil_support_union A B hab).trans (pencil_support_union A B hsa).symm
        rw [← heab, Finset.union_self] at h
        rw [h]
        exact Finset.subset_union_left
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard s hs (hn s hs), hcard a ha (hn a ha)])
    intro s hs t ht _ _
    exact (hall s hs).trans (hall t ht).symm

end
end Paper2.HeightOne.Cyclic
