import Paper2.ExactInput.Recognition.NativeTargetPacking
import Holant.Proofs.Recognition.RuntimeSupportTable

/-! Exact semantic data for the syntactically regrouped target tuple. The
desired target tables are retained explicitly; root representation is required
only at the real flat tuple lookup address. -/
namespace Paper2.ExactInput.Recognition.NativeTargetPacking
open Holant Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
noncomputable section

theorem source_row (d : RuntimeSupportTable.Data) (i : Fin d.count) :
    (RuntimeSupportTable.original d).1.getD i.val (0,[]) =
      (d.arity i,(SparseTransform.allWords (d.arity i)).map (d.input i)) := by
  simp [RuntimeSupportTable.original,OriginalFamilyPackingSource.fromSource,
    List.getD_eq_getElem?_getD,i.isLt,List.getElem_finRange]
  rw [List.getElem_finRange]
  rfl

theorem source_count (d : RuntimeSupportTable.Data) :
    (RuntimeSupportTable.original d).1.length=d.count := by
  simp [RuntimeSupportTable.original,OriginalFamilyPackingSource.fromSource]

def targetOrdinal (d : RuntimeSupportTable.Data) (i : Fin d.count)
    (x : Fin (d.arity i) → Bool) : ℕ :=
  offset (RuntimeSupportTable.original d).1 i.val +
    (SparseTransform.allWords (d.arity i)).idxOf x

def targetInput (d : RuntimeSupportTable.Data) (cs : List Root) :
    OriginalFamilyInput.Input d.arity := fun i x =>
  (((reshape (RuntimeSupportTable.original d,cs)).1.getD i.val (0,[])).2).getD
    ((SparseTransform.allWords (d.arity i)).idxOf x) defaultRoot

theorem targetInput_at (d : RuntimeSupportTable.Data) (cs : List Root)
    (i : Fin d.count) (x : Fin (d.arity i) → Bool) :
    targetInput d cs i x = cs.getD (targetOrdinal d i x) defaultRoot := by
  apply row_entry (RuntimeSupportTable.original d,cs) i.val _
  · rw [source_count]; exact i.isLt
  · rw [source_row,List.length_map]
    exact List.idxOf_lt_length_of_mem (SparseTransform.mem_allWords x)

private theorem dense_rebuild (n : ℕ) (cs : List Root)
    (hc : cs.length=(SparseTransform.allWords n).length) :
    (SparseTransform.allWords n).map
      (fun x => cs.getD ((SparseTransform.allWords n).idxOf x) defaultRoot) = cs := by
  classical
  apply List.ext_getElem
  · simp [hc]
  · intro i hi hj
    have hw : i < (SparseTransform.allWords n).length := by simpa using hi
    simp only [List.getElem_map]
    rw [(SparseTransform.allWords_nodup n).idxOf_getElem i]
    simp [List.getD_eq_getElem?_getD,hj]

theorem target_dense_row (d : RuntimeSupportTable.Data) (cs : List Root) (i : Fin d.count) :
    (SparseTransform.allWords (d.arity i)).map (targetInput d cs i) =
      ((reshape (RuntimeSupportTable.original d,cs)).1.getD i.val (0,[])).2 := by
  apply dense_rebuild
  rw [row_length (RuntimeSupportTable.original d,cs) i.val
    (by rw [source_count]; exact i.isLt),source_row,List.length_map]

def targetData (d : RuntimeSupportTable.Data)
    (G : (i : Fin d.count) → Signature AlgebraicComplex (d.arity i))
    (cs : List Root)
    (hrep : ∀ i x, (cs.getD (targetOrdinal d i x) defaultRoot).Represents (G i x : ℂ)) :
    RuntimeSupportTable.Data where
  count := d.count
  arity := d.arity
  G := G
  input := targetInput d cs
  represented i x := by rw [targetInput_at]; exact hrep i x

theorem targetData_original (d : RuntimeSupportTable.Data)
    (G : (i : Fin d.count) → Signature AlgebraicComplex (d.arity i))
    (cs : List Root)
    (hrep : ∀ i x, (cs.getD (targetOrdinal d i x) defaultRoot).Represents (G i x : ℂ)) :
    reshape (RuntimeSupportTable.original d,cs) =
      RuntimeSupportTable.original (targetData d G cs hrep) := by
  change (family (RuntimeSupportTable.original d,cs),false) =
    ((List.finRange d.count).map (fun i =>
      (d.arity i,(SparseTransform.allWords (d.arity i)).map (targetInput d cs i))),false)
  congr 1
  rw [← List.ofFn_id,List.map_ofFn]
  apply List.ext_getElem
  · simp [family_length,source_count]
  · intro j hj hk
    have hjs : j < (RuntimeSupportTable.original d).1.length := by
      simpa only [family_length] using hj
    have hjd : j < d.count := by simpa only [source_count] using hjs
    let i : Fin d.count := ⟨j,hjd⟩
    have hrow := row_at (RuntimeSupportTable.original d,cs) j hjs
    have ha := row_arity (RuntimeSupportTable.original d,cs) j hjs
    have hd := target_dense_row d cs i
    rw [source_row d i] at ha
    have he : (family (RuntimeSupportTable.original d,cs)).getD j (0,[]) =
        (d.arity i,(SparseTransform.allWords (d.arity i)).map (targetInput d cs i)) := by
      apply Prod.ext
      · exact ha
      · exact hd.symm
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,
      Option.getD_some,List.getElem_ofFn,Function.comp_apply,id_eq] using he

end
end Paper2.ExactInput.Recognition.NativeTargetPacking
