import Paper2.ExactInput.Recognition.NativeKSystemLayout
import Paper2.ExactInput.Recognition.NativeTargetData

/-! The actual flat target table address agrees with the original dense
coefficient catalogue address. -/
namespace Paper2.ExactInput.Recognition.NativeKSystemLayout
set_option backward.isDefEq.respectTransparency false
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1

private theorem idxOf_flatMap_unique {A B : Type} [DecidableEq A] [DecidableEq B]
    (xs : List A) (f : A → List B) (a : A) (b : B)
    (ha : a ∈ xs) (hb : b ∈ f a)
    (ho : ∀ a' ∈ xs, a' ≠ a → b ∉ f a') :
    (xs.flatMap f).idxOf b =
      (((xs.take (xs.idxOf a)).map (fun z => (f z).length)).sum) + (f a).idxOf b := by
  induction xs with
  | nil => simp at ha
  | cons h t ih =>
    by_cases he : h = a
    · subst h
      simp only [List.flatMap_cons,List.idxOf_cons_self,List.take_zero,List.map_nil,
        List.sum_nil,Nat.zero_add]
      exact List.idxOf_append_of_mem hb
    · have hat : a ∈ t := (List.mem_cons.mp ha).resolve_left (Ne.symm he)
      have hot : ∀ a' ∈ t, a' ≠ a → b ∉ f a' :=
        fun a' hm hn => ho a' (List.mem_cons_of_mem _ hm) hn
      rw [List.flatMap_cons,List.idxOf_append_of_notMem (ho h (by simp) he),
        List.idxOf_cons_ne _ he,List.take_succ_cons,List.map_cons,List.sum_cons,
        ih hat hot]
      omega

private theorem coefficient_idx_prefix {s : ℕ} (arity : Fin s → ℕ)
    (i : Fin s) (x : Fin (arity i) → Bool) :
    (coefficientCatalogue arity).idxOf ⟨.inl i,x⟩ =
      (((List.finRange s).take i.val).map
        (fun j => (SparseTransform.allWords (arity j)).length)).sum +
      (SparseTransform.allWords (arity i)).idxOf x := by
  let f := fun j : Fin s => (SparseTransform.allWords (arity j)).map
    (fun y => (⟨.inl j,y⟩ : LocalAffineVariableLayout.Parameters arity))
  have hb : (⟨.inl i,x⟩ : LocalAffineVariableLayout.Parameters arity) ∈ f i :=
    List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩
  have ho : ∀ j ∈ List.finRange s, j ≠ i →
      (⟨.inl i,x⟩ : LocalAffineVariableLayout.Parameters arity) ∉ f j := by
    intro j _ hji hm
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hm
    have hfst := congrArg Sigma.fst hy
    exact hji (Sum.inl.inj hfst)
  have h := idxOf_flatMap_unique (List.finRange s) f i
    (⟨.inl i,x⟩ : LocalAffineVariableLayout.Parameters arity) (List.mem_finRange i) hb ho
  rw [List.idxOf_finRange] at h
  simp only [f,List.length_map] at h
  rw [OriginalCatalogueSource.idxOf_map_injective _ (by
    intro a b hab
    exact eq_of_heq (Sigma.mk.inj_iff.mp hab).2)] at h
  exact h

theorem coefficient_address_offset {s : ℕ} (arity : Fin s → ℕ)
    (input : OriginalFamilyInput.Input arity) (i : Fin s) (x : Fin (arity i) → Bool) :
    (LocalAffineVariableLayout.address arity ⟨.inl i,x⟩).val =
      NativeTargetPacking.offset (OriginalCatalogueSource.family arity input) i.val +
        (SparseTransform.allWords (arity i)).idxOf x := by
  rw [coefficient_address_eq,coefficient_idx_prefix]
  congr 1
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro j hj hk
    have hji : j < i.val := by simpa only [List.length_map,List.length_take,
      List.length_finRange,Nat.min_eq_left (Nat.le_of_lt i.isLt)] using hj
    have hjs : j < s := hji.trans i.isLt
    simp only [List.getElem_map,List.getElem_range]
    simp [OriginalCatalogueSource.family,OriginalFamilyPackingSource.fromSource,
      List.getD_eq_getElem?_getD,hjs,List.getElem_finRange]
    exact congrArg (fun z : Fin s => (SparseTransform.allWords (arity z)).length)
      (List.getElem_take (xs := List.finRange s) (j := i.val) (i := j))

theorem targetOrdinal_address (d : RuntimeSupportTable.Data) (i : Fin d.count)
    (x : Fin (d.arity i) → Bool) :
    NativeTargetPacking.targetOrdinal d i x =
      (LocalAffineVariableLayout.address d.arity ⟨.inl i,x⟩).val := by
  exact (coefficient_address_offset d.arity d.input i x).symm

end Paper2.ExactInput.Recognition.NativeKSystemLayout
