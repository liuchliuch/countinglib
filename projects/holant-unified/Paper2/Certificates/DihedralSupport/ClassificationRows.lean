module
public import Paper2.Certificates.DihedralSupport.ClassificationSemantics
public import Paper2.Certificates.DihedralSupport.AllRows
public import Paper2.Certificates.DihedralSupport.ClassificationAssembly
public import Paper2.Certificates.DihedralSupport.ClassificationChecked
public import Mathlib.Data.Finset.Card

/-! Exhaustiveness of the six-port support certificate. Every actual bounded
support is assembled from four arbitrary sixteen-bit slices. The two local
union tests place these slices in the proved complete local list; the other
fourteen tests then invoke the checked row equality. No certificate-generation
assumption occurs in the coverage theorem. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport


def equalSlices (m : Nat) : Nat × Nat :=
  (m % 65536, m / 281474976710656 % 65536)
def mixedSlices (m : Nat) : Nat × Nat :=
  (m / 65536 % 65536, m / 4294967296 % 65536)

theorem equal_projection (m : Nat) :
    project (chunksFor 0 false) m = (equalSlices m).1 ||| (equalSlices m).2 := by
  simp [chunksFor, pairChunks, chunks0_0, project, Chunk.copy,
    equalSlices, Nat.shiftRight_eq_div_pow]

theorem mixed_projection (m : Nat) :
    project (chunksFor 0 true) m = (mixedSlices m).1 ||| (mixedSlices m).2 := by
  simp [chunksFor, pairChunks, chunks0_1, project, Chunk.copy,
    mixedSlices, Nat.shiftRight_eq_div_pow]

theorem admissible_equalSlices {m : Nat} (h : AdmissibleMask m) :
    equalSlices m ∈ localChoices := by
  apply mem_localChoices
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · simpa only [equal_projection, equalSlices] using h.2 0 false

theorem admissible_mixedSlices {m : Nat} (h : AdmissibleMask m) :
    mixedSlices m ∈ localChoices := by
  apply mem_localChoices
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · simpa only [mixed_projection, mixedSlices] using h.2 0 true


theorem admissible_mem_survivorMasks {m : Nat} (h : AdmissibleMask m) :
    m ∈ survivorMasks := by
  have he := admissible_equalSlices h
  have hm := admissible_mixedSlices h
  rw [localData_complete] at he hm
  obtain ⟨i, hi, hie⟩ := List.mem_map.mp he
  obtain ⟨j, hj, hjm⟩ := List.mem_map.mp hm
  have hib : i < 1045 := List.mem_range.mp hi
  have hjb : j < 1045 := List.mem_range.mp hj
  have hassemble : assemble (localAt i) (localAt j) = m := by
    rw [hie, hjm]
    exact assemble_slices m h.1
  have hcandidate : m ∈ rowCandidates i := by
    exact List.mem_map.mpr ⟨j, hj, hassemble⟩
  have hfiltered : m ∈ (rowCandidates i).filter goodAll :=
    List.mem_filter.mpr ⟨hcandidate, all_goodAt_goodAll (admissible_goodAt h)⟩
  rw [row_filter_eq ⟨i, hib⟩] at hfiltered
  obtain ⟨k, hk, heq⟩ := List.mem_map.mp hfiltered
  have hkb : k < rowLength i := List.mem_range.mp hk
  have hrange := row_bounds ⟨i, hib⟩
  change rowStart i + rowLength i ≤ 873 at hrange
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨rowStart i + k, List.mem_range.mpr (by omega), heq⟩


theorem survivorMasks_admissible {m : Nat} (h : m ∈ survivorMasks) :
    AdmissibleMask m := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  exact survivors_admissible_checked ⟨i, List.mem_range.mp hi⟩

theorem admissible_iff_survivorMasks (m : Nat) :
    AdmissibleMask m ↔ m ∈ survivorMasks :=
  ⟨admissible_mem_survivorMasks, survivorMasks_admissible⟩


/-- Exactly 873 masks satisfy the original local support condition, and the
encoding of every arbitrary admissible six-bit support is one of them. -/
theorem support_enumeration (S : Support6) :
    (AdmissibleSupport S ↔ encodeSupport S ∈ survivorMasks) ∧ survivorMasks.card = 873 :=
  ⟨(admissibleSupport_iff_mask S).trans (admissible_iff_survivorMasks _), survivorMasks_card⟩

end Paper2.Certificates.DihedralSupport

