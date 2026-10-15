import Holant.Proofs.Algorithms.TransformRecognition.OriginalCatalogueSource

/-! Exact source coefficient prefixes and literal root binding addresses for
the native K-table certificate request. The existing dense table order is
retained, including empty families and nullary signatures. -/
namespace Paper2.ExactInput.Recognition.NativeKSystemLayout
set_option backward.isDefEq.respectTransparency false
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition

abbrev Root := Holant.LocalDrafts.EffectiveAlgebraic.RootCode
abbrev Packed := OriginalFamilyPackingMachine.Input
variable {s : ℕ} (arity : Fin s → ℕ)

def coefficientCatalogue : List (LocalAffineVariableLayout.Parameters arity) :=
  (List.finRange s).flatMap (fun i =>
    (SparseTransform.allWords (arity i)).map (fun x => ⟨.inl i,x⟩))

def edgeCatalogue : List (LocalAffineVariableLayout.Parameters arity) :=
  (SparseTransform.allWords 2).map (fun x => ⟨.inr (),x⟩)

theorem catalogue_prefix : LocalAffineVariableLayout.catalogue arity =
    coefficientCatalogue arity ++ edgeCatalogue arity := by
  simp only [LocalAffineVariableLayout.catalogue,ProductVariableLayout.slots,
    List.flatMap_append,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,coefficientCatalogue,edgeCatalogue,
    ProductVariableLayout.slotArity,Sum.elim_inl,Sum.elim_inr]

theorem mem_coefficientCatalogue (i : Fin s) (x : Fin (arity i) → Bool) :
    (⟨.inl i,x⟩ : LocalAffineVariableLayout.Parameters arity) ∈ coefficientCatalogue arity :=
  List.mem_flatMap.mpr ⟨i,List.mem_finRange i,
    List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩⟩

theorem coefficient_address_eq (i : Fin s) (x : Fin (arity i) → Bool) :
    (LocalAffineVariableLayout.address arity ⟨.inl i,x⟩).val =
      (coefficientCatalogue arity).idxOf ⟨.inl i,x⟩ := by
  change (LocalAffineVariableLayout.catalogue arity).idxOf _ = _
  rw [catalogue_prefix,List.idxOf_append_of_mem (mem_coefficientCatalogue arity i x)]

theorem coefficientAddress_lt (i : Fin s) (x : Fin (arity i) → Bool) :
    (LocalAffineVariableLayout.address arity ⟨.inl i,x⟩).val <
      (coefficientCatalogue arity).length := by
  rw [coefficient_address_eq]
  exact List.idxOf_lt_length_iff.mpr (mem_coefficientCatalogue arity i x)

def familyFlat (r : Packed) : List Root := r.1.flatMap Prod.snd

theorem coefficientFlat_exact (input : OriginalFamilyInput.Input arity) (flag : Bool) :
    familyFlat (OriginalFamilyPackingSource.fromSource arity input flag) =
      (coefficientCatalogue arity).map (OriginalFamilyPackingSource.entryCode arity input flag) := by
  simp only [familyFlat,OriginalFamilyPackingSource.fromSource,coefficientCatalogue,
    List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  change (SparseTransform.allWords (arity i)).map (input i) =
    ((SparseTransform.allWords (arity i)).map
      (fun x => (⟨.inl i,x⟩ : LocalAffineVariableLayout.Parameters arity))).map _
  rw [List.map_map]
  rfl

theorem coefficientFlat_length (input : OriginalFamilyInput.Input arity) (flag : Bool) :
    (familyFlat (OriginalFamilyPackingSource.fromSource arity input flag)).length =
      (coefficientCatalogue arity).length := by rw [coefficientFlat_exact,List.length_map]

theorem coefficientRoot_at (input : OriginalFamilyInput.Input arity) (flag : Bool)
    (i : Fin s) (x : Fin (arity i) → Bool) (fallback : Root) :
    (familyFlat (OriginalFamilyPackingSource.fromSource arity input flag)).getD
      (LocalAffineVariableLayout.address arity ⟨.inl i,x⟩).val fallback = input i x := by
  rw [coefficientFlat_exact,coefficient_address_eq]
  have hi := List.idxOf_lt_length_iff.mpr (mem_coefficientCatalogue arity i x)
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),List.getElem_map,
    List.getElem_idxOf]
  rfl

theorem address_zero (input : OriginalFamilyInput.Input arity)
    (p : LocalAffineVariableLayout.Parameters arity) :
    OriginalCatalogueMachine.address
      (0,OriginalCatalogueMachine.catalogue (OriginalCatalogueSource.family arity input),
        OriginalCatalogueSource.key arity p) =
      5+(LocalAffineVariableLayout.address arity p).val := by
  rw [OriginalCatalogueSource.catalogue_exact]
  change 5+0+(List.map (OriginalCatalogueSource.key arity)
    (LocalAffineVariableLayout.catalogue arity)).idxOf (OriginalCatalogueSource.key arity p) = _
  rw [OriginalCatalogueSource.idxOf_map_injective _
    (OriginalCatalogueSource.key_injective arity)]
  rfl

theorem table_zero (input : OriginalFamilyInput.Input arity) (i : Fin s) :
    OriginalAddressTablesMachine.table (OriginalCatalogueSource.family arity input,0,i.val) =
      (SparseTransform.allWords (arity i)).map
        (fun x => (List.ofFn x,5+(LocalAffineVariableLayout.address arity ⟨.inl i,x⟩).val)) := by
  change (OriginalCatalogueMachine.atVertex (OriginalCatalogueSource.family arity input)
    (OriginalCatalogueSource.slotNumber (.inl i))).map _ = _
  rw [OriginalCatalogueSource.atVertex_exact]
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro x _
  rw [address_zero]
  rfl

def requestRoots (r : Packed) (cs : List Root) : List Root :=
  OriginalFamilyPackingMachine.roots r ++ cs

def requestWidth (r : Packed) (cs : List Root) : ℕ := 5+(requestRoots r cs).length

def binding (r : Packed) (cs : List Root) (j : Fin (requestRoots r cs).length) :
    Fin (requestWidth r cs) := Fin.natAdd 5 j

@[simp] theorem binding_val (r : Packed) (cs : List Root) (j : Fin (requestRoots r cs).length) :
    (binding r cs j).val = 5+j.val := rfl

def sourceIndex (r : Packed) (cs : List Root)
    (j : Fin (OriginalFamilyPackingMachine.roots r).length) : Fin (requestRoots r cs).length :=
  ⟨j.val,by simpa only [requestRoots,List.length_append] using
    j.isLt.trans_le (Nat.le_add_right _ _)⟩

def targetIndex (r : Packed) (cs : List Root) (j : Fin cs.length) :
    Fin (requestRoots r cs).length :=
  ⟨(OriginalFamilyPackingMachine.roots r).length+j.val,
    by simpa only [requestRoots,List.length_append] using Nat.add_lt_add_left j.isLt _⟩

@[simp] theorem sourceIndex_val (r : Packed) (cs : List Root)
    (j : Fin (OriginalFamilyPackingMachine.roots r).length) :
    (sourceIndex r cs j).val=j.val := rfl

@[simp] theorem targetIndex_val (r : Packed) (cs : List Root) (j : Fin cs.length) :
    (targetIndex r cs j).val=(OriginalFamilyPackingMachine.roots r).length+j.val := rfl

theorem sourceRoot_at (r : Packed) (cs : List Root)
    (j : Fin (OriginalFamilyPackingMachine.roots r).length) (fallback : Root) :
    (requestRoots r cs).getD (sourceIndex r cs j).val fallback =
      (OriginalFamilyPackingMachine.roots r).getD j.val fallback :=
  List.getD_append _ _ _ _ j.isLt

theorem targetRoot_at (r : Packed) (cs : List Root) (j : Fin cs.length) (fallback : Root) :
    (requestRoots r cs).getD (targetIndex r cs j).val fallback = cs.get j := by
  change (OriginalFamilyPackingMachine.roots r ++ cs).getD
    ((OriginalFamilyPackingMachine.roots r).length+j.val) fallback = cs.get j
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem request_roots_prefix (r : Packed) (cs : List Root) :
    (requestRoots r cs).take (OriginalFamilyPackingMachine.roots r).length =
      OriginalFamilyPackingMachine.roots r := by simp [requestRoots]

def descriptorIndex (input : OriginalFamilyInput.Input arity) (flag : Bool) (cs : List Root)
    (j : Fin (OriginalAffineSystem.Entries arity+2)) :
    Fin (requestRoots (OriginalFamilyPackingSource.fromSource arity input flag) cs).length :=
  ⟨j.val,by
    rw [requestRoots,List.length_append,OriginalFamilyPackingSource.roots_exact,List.length_ofFn]
    exact j.isLt.trans_le (Nat.le_add_right _ _)⟩

def descriptorBinding (input : OriginalFamilyInput.Input arity) (flag : Bool) (cs : List Root)
    (j : Fin (OriginalAffineSystem.Entries arity+2)) :
    Fin (requestWidth (OriginalFamilyPackingSource.fromSource arity input flag) cs) :=
  binding _ cs (descriptorIndex arity input flag cs j)

@[simp] theorem descriptorBinding_val (input : OriginalFamilyInput.Input arity) (flag : Bool)
    (cs : List Root) (j : Fin (OriginalAffineSystem.Entries arity+2)) :
    (descriptorBinding arity input flag cs j).val=5+j.val := rfl

theorem descriptorRoot_at (input : OriginalFamilyInput.Input arity) (flag : Bool) (cs : List Root)
    (j : Fin (OriginalAffineSystem.Entries arity+2)) (fallback : Root) :
    (requestRoots (OriginalFamilyPackingSource.fromSource arity input flag) cs).getD
      (descriptorIndex arity input flag cs j).val fallback =
      OriginalVariableLayout.descriptors (OriginalFamilyInput.pack arity input flag) j := by
  change (OriginalFamilyPackingMachine.roots _ ++ cs).getD j.val _ = _
  rw [OriginalFamilyPackingSource.roots_exact]
  have hj : j.val < (List.ofFn (OriginalVariableLayout.descriptors
      (OriginalFamilyInput.pack arity input flag))).length := by
    simpa only [List.length_ofFn] using j.isLt
  rw [List.getD_append _ _ _ _ hj]
  exact Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn _ j fallback

theorem coefficientDescriptorRoot_at (input : OriginalFamilyInput.Input arity) (flag : Bool)
    (cs : List Root) (i : Fin s) (x : Fin (arity i) → Bool) (fallback : Root) :
    (requestRoots (OriginalFamilyPackingSource.fromSource arity input flag) cs).getD
      (LocalAffineVariableLayout.address arity ⟨.inl i,x⟩).val fallback = input i x := by
  have h := descriptorRoot_at arity input flag cs
    (Fin.castAdd 2 (LocalAffineVariableLayout.address arity ⟨.inl i,x⟩)) fallback
  simpa only [descriptorIndex,Fin.val_castAdd,OriginalVariableLayout.descriptors,
    Fin.addCases_left,OriginalFamilyInput.pack,LocalAffineVariableLayout.get_address] using h

end Paper2.ExactInput.Recognition.NativeKSystemLayout
