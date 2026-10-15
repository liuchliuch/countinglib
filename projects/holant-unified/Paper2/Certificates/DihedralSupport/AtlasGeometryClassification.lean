import Paper2.Certificates.DihedralSupport.AtlasGeometryAllRows
import Paper2.Certificates.DihedralSupport.AtlasGeometryCompatibility
import Paper2.Certificates.DihedralSupport.AtlasGeometryPairCheck
import Paper2.Certificates.DihedralSupport.AtlasGeometryRichCheck
import Paper2.Certificates.DihedralSupport.AtlasCountsIncidence

/-! Exhaustive geometry of the literal V/E atlas in Q(ω). The only finite
inputs used here have independent kernel-checked minor certificates. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometryClassification
open AtlasCounts AtlasVectors AtlasGeometry CyclotomicArithmetic AtlasGeometryCheck

def v (l : PointLabel) : Coordinate → Scalar := vector omega l
def index (l : PointLabel) : ℕ := pointList.idxOf l

theorem index_lt (l : PointLabel) : index l < 66 :=
  point_index_lt l (pointList_complete l)

theorem label_index (l : PointLabel) : pointLabel (index l) = l :=
  pointLabel_index l (pointList_complete l)

theorem point_index (l : PointLabel) : point (index l) = v l := by
  funext x
  exact (point_compatibility ⟨index l,index_lt l⟩ x).trans
    (congrArg (fun t => vector omega t x) (label_index l))

theorem index_injective : Function.Injective index := by
  intro l m h
  have hh := congrArg pointLabel h
  simpa only [label_index] using hh

theorem pair_independent (l m : PointLabel) (h : l ≠ m) :
    ∃ a b, minor2 (v l) (v m) a b ≠ 0 := by
  have hn : index l ≠ index m := fun hi => h (index_injective hi)
  rcases lt_or_gt_of_ne hn with hij | hji
  · obtain ⟨a,b,hab⟩ := checkPairs_sound pairs_checked hij (index_lt m)
    exact ⟨a,b,by simpa only [point_index] using hab⟩
  · obtain ⟨a,b,hab⟩ := checkPairs_sound pairs_checked hji (index_lt l)
    refine ⟨a,b,?_⟩
    intro hz
    apply hab
    rw [point_index,point_index]
    dsimp [minor2] at *
    linear_combination -hz

private theorem sorted_classification (i j k : ℕ) (hij : i < j) (hjk : j < k)
    (hk : k < 66) (hz : ZeroMinors (point i) (point j) (point k)) :
    ∃ r : RichLabel, richSet r = {pointLabel i,pointLabel j,pointLabel k} := by
  exact checkRow_sound (all_rows_checked ⟨i,by omega⟩) hij hjk hk hz

private theorem index_classification (i j k : ℕ) (hi : i < 66) (hj : j < 66)
    (hk : k < 66) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hz : ZeroMinors (point i) (point j) (point k)) :
    ∃ r : RichLabel, richSet r = {pointLabel i,pointLabel j,pointLabel k} := by
  rcases lt_or_gt_of_ne hij with h1 | h1
  · rcases lt_or_gt_of_ne hjk with h2 | h2
    · exact sorted_classification i j k h1 h2 hk hz
    · rcases lt_or_gt_of_ne hik with h3 | h3
      · obtain ⟨r,hr⟩ := sorted_classification i k j h3 h2 hj
          (zeroMinors_swap_right hz)
        refine ⟨r,hr.trans ?_⟩
        ext x; simp; tauto
      · obtain ⟨r,hr⟩ := sorted_classification k i j h3 h1 hj
          (zeroMinors_swap_left (zeroMinors_swap_right hz))
        refine ⟨r,hr.trans ?_⟩
        ext x; simp; tauto
  · rcases lt_or_gt_of_ne hik with h2 | h2
    · obtain ⟨r,hr⟩ := sorted_classification j i k h1 h2 hk
        (zeroMinors_swap_left hz)
      refine ⟨r,hr.trans ?_⟩
      ext x; simp; tauto
    · rcases lt_or_gt_of_ne hjk with h3 | h3
      · obtain ⟨r,hr⟩ := sorted_classification j k i h3 h2 hi
          (zeroMinors_swap_right (zeroMinors_swap_left hz))
        refine ⟨r,hr.trans ?_⟩
        ext x; simp; tauto
      · obtain ⟨r,hr⟩ := sorted_classification k j i h3 h1 hi
          (zeroMinors_swap_left (zeroMinors_swap_right (zeroMinors_swap_left hz)))
        refine ⟨r,hr.trans ?_⟩
        ext x; simp; tauto

/-- Every dependent triple of distinct atlas points is exactly one of the
four displayed geometric types; the exclusion is over the genuine field. -/
theorem classify (l m n : PointLabel) (hlm : l ≠ m) (hln : l ≠ n) (hmn : m ≠ n)
    (hz : ZeroMinors (v l) (v m) (v n)) :
    ∃ r : RichLabel, richSet r = {l,m,n} := by
  have hi : index l ≠ index m := fun h => hlm (index_injective h)
  have hj : index l ≠ index n := fun h => hln (index_injective h)
  have hk : index m ≠ index n := fun h => hmn (index_injective h)
  obtain ⟨r,hr⟩ := index_classification (index l) (index m) (index n)
    (index_lt l) (index_lt m) (index_lt n) hi hj hk
    (by simpa only [point_index] using hz)
  exact ⟨r,by simpa only [label_index] using hr⟩

theorem rich_onLine (r : RichLabel) :
    OnLine (v (richPoints r 0)) (v (richPoints r 1)) (v (richPoints r 2)) := by
  have hi := rich_index_lt r (richList_complete r)
  have hh := List.all_eq_true.mp rich_lines_checked (richList.idxOf r)
    (List.mem_range.mpr hi)
  have hr := checkRich_sound hh
  rw [richLabel_index r (richList_complete r)] at hr
  change OnLine (point (index (richPoints r 0)))
    (point (index (richPoints r 1))) (point (index (richPoints r 2))) at hr
  simpa only [point_index] using hr

theorem onLine_of_mem (r : RichLabel) (l : PointLabel) (h : l ∈ richSet r) :
    OnLine (v (richPoints r 0)) (v (richPoints r 1)) (v l) := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
  fin_cases j
  · exact ⟨1,0,by simp⟩
  · exact ⟨0,1,by simp⟩
  · exact rich_onLine r

/-- Every rich line contains exactly the three listed projective points.
This derives exact incidence from the exhaustive minor certificates. -/
theorem rich_line_membership (r : RichLabel) (l : PointLabel) :
    OnLine (v (richPoints r 0)) (v (richPoints r 1)) (v l) ↔ l ∈ richSet r := by
  refine ⟨?_,onLine_of_mem r l⟩
  intro h
  by_cases h0 : l = richPoints r 0
  · subst l; exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  by_cases h1 : l = richPoints r 1
  · subst l; exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
  have h01 : richPoints r 0 ≠ richPoints r 1 := fun hh => by
    have := richPoints_distinct r hh
    norm_num at this
  obtain ⟨s,hs⟩ := classify (richPoints r 0) (richPoints r 1) l h01
    (Ne.symm h0) (Ne.symm h1) (fun a b c => minor3_eq_zero_of_onLine h a b c)
  have h0r : richPoints r 0 ∈ richSet r :=
    Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  have h1r : richPoints r 1 ∈ richSet r :=
    Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
  have h0s : richPoints r 0 ∈ richSet s := by rw [hs]; simp
  have h1s : richPoints r 1 ∈ richSet s := by rw [hs]; simp
  have hrs := richSet_pair_unique h01 h0r h1r h0s h1s
  rw [hrs,hs]
  simp

theorem collinear_iff (l m n : PointLabel) (hlm : l ≠ m) (hln : l ≠ n)
    (hmn : m ≠ n) : OnLine (v l) (v m) (v n) ↔
      ∃ r : RichLabel, richSet r = {l,m,n} := by
  refine ⟨fun h => classify l m n hlm hln hmn
    (fun a b c => minor3_eq_zero_of_onLine h a b c),?_⟩
  rintro ⟨r,hr⟩
  have hl : l ∈ richSet r := by rw [hr]; simp
  have hm : m ∈ richSet r := by rw [hr]; simp
  have hn : n ∈ richSet r := by rw [hr]; simp
  have hz := zeroMinors_of_three_onLine (onLine_of_mem r l hl)
    (onLine_of_mem r m hm) (onLine_of_mem r n hn)
  obtain ⟨a,b,hab⟩ := pair_independent l m hlm
  exact (onLine_iff_zeroMinors hab).mpr hz

end Paper2.Certificates.DihedralSupport.AtlasGeometryClassification

