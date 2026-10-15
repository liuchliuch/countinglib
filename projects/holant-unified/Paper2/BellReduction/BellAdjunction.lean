import Paper2.BellReduction.OccurrenceGraph
import Paper2.HighHeightNormalization.AttachmentNetwork

/-! The last two Bell labels in source Lemma 8.12 are realized by literal
ordered two-vertex paths. The one internal edge is native X. In particular no
Bell matrix is silently treated as a free structural edge. -/
namespace Paper2.BellReduction.BellAdjunction
open HighHeightNormalization
variable {K : Type} [CommRing K]

/-- Two equality vertices with one native-X edge subdivide the native wire. -/
theorem equality_path :
    attachment (1 : Fin 2) (Bell.I (K := K)) (bellTable false false) =
      bellTable true false := by
  funext x
  simp only [attachment,Fintype.sum_bool]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [bellTable,Bell.I,Bell.ordered,Bell.sign,Function.update,h0,h1]

/-- The ordered Y-X-I path is exactly Z, with no discarded sign or scalar. -/
theorem phase_path :
    attachment (1 : Fin 2) (Bell.I (K := K)) (bellTable true true) =
      bellTable false true := by
  funext x
  simp only [attachment,Fintype.sum_bool]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [bellTable,Bell.I,Bell.ordered,Bell.sign,Function.update,h0,h1]

 theorem x_realizable {F : SignatureFamily K}
    (hI : (⟨2,bellTable false false⟩ : AnySignature K) ∈ F) :
    NetworkRealizable F (bellTable true false) := by
  rw [← equality_path]
  exact attachment_realizable (1 : Fin 2) Bell.I (bellTable false false) hI hI

 theorem z_realizable {F : SignatureFamily K}
    (hI : (⟨2,bellTable false false⟩ : AnySignature K) ∈ F)
    (hY : (⟨2,bellTable true true⟩ : AnySignature K) ∈ F) :
    NetworkRealizable F (bellTable false true) := by
  rw [← phase_path]
  exact attachment_realizable (1 : Fin 2) Bell.I (bellTable true true) hY hI

end Paper2.BellReduction.BellAdjunction
