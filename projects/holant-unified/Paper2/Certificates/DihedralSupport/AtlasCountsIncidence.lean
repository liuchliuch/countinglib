import Paper2.Certificates.DihedralSupport.AtlasCounts

/-! Actual incidence of the formulaic rich triples. The Boolean check uses
only the defining labels and their three points; no field arithmetic or
stored accepted triples enter this finite combinatorial assertion. -/
namespace Paper2.Certificates.DihedralSupport.AtlasCounts
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 10000

def pairCode (p : Pair) : ℕ :=
  p.1.1.val * (7 - p.1.1.val) / 2 + (p.1.2.val - p.1.1.val - 1)
def pointCode : PointLabel → ℕ
  | .inl (p,r) => 3 * p.val + r.val
  | .inr (p,r,t) => 12 + 9 * pairCode p + 3 * r.val + t.val

theorem pointCode_list : pointList.map pointCode = List.range 66 := by decide +kernel

theorem pointCode_injective : Function.Injective pointCode := by
  have h : (pointList.map pointCode).Nodup := by rw [pointCode_list]; exact List.nodup_range
  intro p q he
  exact List.inj_on_of_nodup_map h (pointList_complete p) (pointList_complete q) he

def codeSet (r : RichLabel) : Finset ℕ := (richSet r).image pointCode

def incidenceCheck : Bool := richList.zipIdx.all fun r => richList.zipIdx.all fun s =>
  decide (r.2 = s.2 ∨ (codeSet r.1 ∩ codeSet s.1).card ≤ 1)

theorem incidence_checked : incidenceCheck = true := by decide +kernel

theorem richSet_intersection_bound {r s : RichLabel} (hrs : r ≠ s) :
    (richSet r ∩ richSet s).card ≤ 1 := by
  let i := richList.idxOf r
  let j := richList.idxOf s
  have hi : (r,i) ∈ richList.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_idxOf (richList_complete r)
  have hj : (s,j) ∈ richList.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_idxOf (richList_complete s)
  have hij : i ≠ j := by
    intro h
    have hr := List.mk_mem_zipIdx_iff_getElem?.mp hi
    have hs := List.mk_mem_zipIdx_iff_getElem?.mp hj
    rw [h] at hr
    exact hrs (Option.some.inj (hr.symm.trans hs))
  have hr := List.all_eq_true.mp incidence_checked (r,i) hi
  have hs := List.all_eq_true.mp hr (s,j) hj
  have hb : (codeSet r ∩ codeSet s).card ≤ 1 := (of_decide_eq_true hs).resolve_left hij
  have he : (codeSet r ∩ codeSet s).card = (richSet r ∩ richSet s).card := by
    unfold codeSet
    rw [←Finset.image_inter _ _ pointCode_injective,
      Finset.card_image_of_injective _ pointCode_injective]
  rwa [he] at hb

theorem richSet_injective : Function.Injective richSet := by
  intro r s he
  by_contra hn
  have hb := richSet_intersection_bound hn
  rw [he,Finset.inter_self,richSet_card] at hb
  omega

theorem richSet_pair_unique {r s : RichLabel} {p q : PointLabel} (hpq : p ≠ q)
    (hpr : p ∈ richSet r) (hqr : q ∈ richSet r)
    (hps : p ∈ richSet s) (hqs : q ∈ richSet s) : r = s := by
  by_contra hn
  have hs : ({p,q} : Finset PointLabel) ⊆ richSet r ∩ richSet s := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_inter.mpr ⟨hpr,hps⟩
    · have he : a = q := Finset.mem_singleton.mp ha
      subst a
      exact Finset.mem_inter.mpr ⟨hqr,hqs⟩
  have hc := Finset.card_le_card hs
  have hb := richSet_intersection_bound hn
  have hd : ({p,q} : Finset PointLabel).card = 2 := by simp [hpq]
  rw [hd] at hc
  omega

private theorem ordered_image (r : OrderedLabel) :
    Finset.univ.image (orderedPoints r) = richSet r.1 := by
  ext p
  constructor
  · rintro hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨r.2 j,Finset.mem_univ _,rfl⟩
  · rintro hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨r.2.symm j,Finset.mem_univ _,by
      simp [orderedPoints]⟩

theorem orderedPoints_injective : Function.Injective orderedPoints := by
  rintro ⟨r,π⟩ ⟨s,τ⟩ h
  have he : richSet r = richSet s := by
    rw [←ordered_image (r,π),←ordered_image (s,τ),h]
  have hrs := richSet_injective he
  subst s
  have hπτ : π = τ := by
    apply Equiv.ext
    intro j
    exact richPoints_distinct r (congrFun h j)
  subst τ
  rfl

end Paper2.Certificates.DihedralSupport.AtlasCounts

