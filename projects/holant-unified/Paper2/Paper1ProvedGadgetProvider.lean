import Paper2.Paper1ProvedNetwork
import Paper2.SourceFaithful.GadgetAugmentation

/-! Genuine direct gadget augmentation from actual retained native networks.
The finite common field records every original coefficient, every augmented
coefficient, and each nonzero fixed macro scalar. It adds no target resource. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Holant.Algebraic Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
namespace GadgetProvider
variable (L M : Language)
variable (h : ∀ f ∈ M.family, NativeNetworkRealizesUpTo L.family f.2)

def graph (i : Fin M.count) : Paper2.Network AlgebraicComplex (M.arity i.val) :=
  Classical.choose (h _ ⟨i,rfl⟩)
theorem uses (i : Fin M.count) : (graph L M h i).Uses L.family :=
  (Classical.choose_spec (h _ ⟨i,rfl⟩)).1
theorem native (i : Fin M.count) : (graph L M h i).NativeX :=
  (Classical.choose_spec (h _ ⟨i,rfl⟩)).2.1
def scalar (i : Fin M.count) : AlgebraicComplex :=
  Classical.choose (Classical.choose_spec (h _ ⟨i,rfl⟩)).2.2
theorem scalar_nonzero (i : Fin M.count) : scalar L M h i ≠ 0 :=
  (Classical.choose_spec (Classical.choose_spec (h _ ⟨i,rfl⟩)).2.2).1
theorem graph_exact (i : Fin M.count) :
    (graph L M h i).denote = fun x => scalar L M h i * M.signature i x :=
  (Classical.choose_spec (Classical.choose_spec (h _ ⟨i,rfl⟩)).2.2).2

def templates (j : ℕ) : Template := if hj : j < M.count then
  (sourceLabels L (graph L M h ⟨j,hj⟩) (uses L M h ⟨j,hj⟩)).template else
    identityTemplate L.arity 0

theorem wellFormed : ∀ j < M.count, (templates L M h j).WellFormed L.count 1 L.arity := by
  intro j hj
  simpa only [templates,dif_pos hj] using
    (sourceLabels L (graph L M h ⟨j,hj⟩) (uses L M h ⟨j,hj⟩)).wellFormed

theorem boundary (i : Fin M.count) : sourceArity (templates L M h) i.val = M.arity i.val := by
  simp [sourceArity,templates,i.isLt]

abbrev Index := Holant.Complexity.ExactSignatureTables.CoefficientIndex L.count 1 L.arity ⊕
  ((Σ i : Fin M.count, Fin (M.arity i.val) → Bool) ⊕ Fin M.count)

def values : Index L M → AlgebraicComplex
  | .inl (.inl ⟨i,x⟩) => L.signature i x
  | .inl (.inr (_,a,b)) => Signature.disequality a b
  | .inr (.inl ⟨i,x⟩) => M.signature i x
  | .inr (.inr i) => scalar L M h i

theorem algebraic (j : Index L M) : IsAlgebraic ℚ (values L M h j) :=
  Algebra.IsAlgebraic.isAlgebraic _
abbrev field := familyField (values L M h)
abbrev presentation := familyPresentation (values L M h) (algebraic L M h)

def embedding : field L M h →ₗ[ℚ] AlgebraicComplex := (field L M h).val.toLinearMap

def scales (i : Fin M.count) : field L M h :=
  fieldCoefficient (values L M h) (.inr (.inr i))
theorem scales_nonzero (i : Fin M.count) : scales L M h i ≠ 0 := by
  intro hz
  exact scalar_nonzero L M h i (congrArg Subtype.val hz)

def targetTables : ExactSignatureTables (Module.finrank ℚ (field L M h)) L.count 1 L.arity where
  vertex i x := familyCoordinates (values L M h) (algebraic L M h) (.inl (.inl ⟨i,x⟩))
  edge i a b := familyCoordinates (values L M h) (algebraic L M h) (.inl (.inr (i,a,b)))

def ambientSource (i : Fin M.count) : Holant.Signature AlgebraicComplex
    (sourceArity (templates L M h) i.val) := fun x =>
  M.signature i (fun j => x (Fin.cast (boundary L M h i).symm j))

def sourceSignatures (i : Fin M.count) : Holant.Signature
    (Fin (Module.finrank ℚ (field L M h)) → ℚ) (sourceArity (templates L M h) i.val) := fun x =>
  familyCoordinates (values L M h) (algebraic L M h)
    (.inr (.inl ⟨i,fun j => x (Fin.cast (boundary L M h i).symm j)⟩))

 theorem templateDenote_congr (t u : Template) (ht : t = u)
    (hw : t.WellFormed L.count 1 L.arity) (hu : u.WellFormed L.count 1 L.arity) :
    HEq (t.network hw (signatures L) (kernels .nativeX)).denote
      (u.network hu (signatures L) (kernels .nativeX)).denote := by
  cases ht
  rfl

 theorem macro_exact (i : Fin M.count) :
    ((templates L M h i.val).network (wellFormed L M h i.val i.isLt)
      (fun j x => (presentation L M h).decode ((targetTables L M h).vertex j x))
      (fun j u v => (presentation L M h).decode ((targetTables L M h).edge j u v))).denote =
        (fun x => scales L M h i * (presentation L M h).decode (sourceSignatures L M h i x)) := by
  apply funext
  intro x
  apply Subtype.ext
  change (field L M h).subtype _ = _
  rw [← Holant.Network.denote_map (field L M h).subtype]
  have hm : (((templates L M h i.val).network (wellFormed L M h i.val i.isLt)
      (fun j x => (presentation L M h).decode ((targetTables L M h).vertex j x))
      (fun j u v => (presentation L M h).decode ((targetTables L M h).edge j u v))).map
        (field L M h).subtype) =
      (templates L M h i.val).network (wellFormed L M h i.val i.isLt)
        (signatures L) (kernels .nativeX) := by
    unfold Holant.Network.map Template.network
    congr 1
    · funext v y
      exact familyCoordinates_spec (values L M h) (algebraic L M h) _
    · funext e a b
      exact familyCoordinates_spec (values L M h) (algebraic L M h) _
  rw [hm]
  have hn := labelled_denote L (graph L M h i) (uses L M h i) (native L M h i)
  have he : HEq ((templates L M h i.val).network (wellFormed L M h i.val i.isLt)
      (signatures L) (kernels .nativeX)).denote (graph L M h i).denote := by
    have ht : templates L M h i.val =
        (sourceLabels L (graph L M h i) (uses L M h i)).template := by
      simp only [templates,dif_pos i.isLt]
    exact (templateDenote_congr L _ _ ht _ _).trans (heq_of_eq hn)
  have hs : (⟨sourceArity (templates L M h) i.val,
      ((templates L M h i.val).network (wellFormed L M h i.val i.isLt)
        (signatures L) (kernels .nativeX)).denote⟩ : AnySignature AlgebraicComplex) =
      ⟨M.arity i.val,(graph L M h i).denote⟩ := Sigma.ext (boundary L M h i) he
  have hy := Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
    (graph L M h i).denote
    ((templates L M h i.val).network (wellFormed L M h i.val i.isLt)
      (signatures L) (kernels .nativeX)).denote hs.symm (boundary L M h i).symm x
  rw [← hy,graph_exact L M h i]
  change scalar L M h i * M.signature i (fun j => x (Fin.cast (boundary L M h i).symm j)) =
    scalar L M h i * (((familyPresentation (values L M h) (algebraic L M h)).decode
      (familyCoordinates (values L M h) (algebraic L M h)
        (.inr (.inl ⟨i,fun j => x (Fin.cast (boundary L M h i).symm j)⟩)))) : AlgebraicComplex)
  rw [familyCoordinates_spec]
  rfl

abbrev sourceValue := (sourceTables (templates L M h) (targetTables L M h)
  (sourceSignatures L M h)).evaluate (presentation L M h)
abbrev targetValue := (targetTables L M h).evaluate (presentation L M h)

def sourceInput (G : Instance M) :
    Holant.Complexity.ExactSignatureTables.Input M.count 1 (sourceArity (templates L M h)) :=
  ⟨(input M G).val,by
    have hh := (input M G).property
    constructor
    · intro v
      exact ⟨(hh.1 v).1,by rw [boundary L M h ⟨_,(hh.1 v).1⟩]; exact (hh.1 v).2⟩
    · exact hh.2⟩

def inputComputes : Paper2.Complexity.BinaryCompose.Computes (inputEncoding M)
    (Holant.Complexity.RawClosedNetwork.validatedEncoding M.count 1 (sourceArity (templates L M h)))
    (sourceInput L M h) :=
  Paper2.Complexity.FixedFieldMachines.recode (Paper2.Complexity.BinaryCompose.identityComputes
    (inputEncoding M)) id (fun _ => rfl) (fun G => (input_bytes M G).symm)

 theorem target_correct (r : SourceInput L) : embedding L M h (targetValue L M h r) =
    Problem.value .nativeX L ((inputIso L).symm r) := by
  change (targetValue L M h r : AlgebraicComplex) = _
  rw [targetValue,Holant.Complexity.ExactSignatureTables.evaluate_eq_decoded]
  change (field L M h).subtype _ = _
  rw [← Holant.Network.denote_map (field L M h).subtype]
  have hm : ((r.val.realize r.property
      (fun j x => (presentation L M h).decode ((targetTables L M h).vertex j x))
      (fun j u v => (presentation L M h).decode ((targetTables L M h).edge j u v))).map
        (field L M h).subtype) = r.val.realize r.property (signatures L) (kernels .nativeX) := by
    unfold Holant.Network.map Holant.Complexity.RawClosedNetwork.realize
    congr 1
    · funext v x
      exact familyCoordinates_spec (values L M h) (algebraic L M h) _
    · funext e a b
      exact familyCoordinates_spec (values L M h) (algebraic L M h) _
  rw [hm]
  have hn := network_value .nativeX L ((inputIso L).symm r)
  change (((inputIso L) ((inputIso L).symm r)).val.realize
    (((inputIso L) ((inputIso L).symm r)).property) (signatures L) (kernels .nativeX)).denote Fin.elim0 = _ at hn
  rwa [Equiv.apply_symm_apply] at hn

 theorem source_correct (G : Instance M) :
    embedding L M h (sourceValue L M h (sourceInput L M h G)) = Problem.value .nativeX M G := by
  change (sourceValue L M h (sourceInput L M h G) : AlgebraicComplex) = _
  rw [sourceValue,Holant.Complexity.ExactSignatureTables.evaluate_eq_decoded]
  change (field L M h).subtype _ = _
  rw [← Holant.Network.denote_map (field L M h).subtype]
  have hm : (((sourceInput L M h G).val.realize (sourceInput L M h G).property
      (fun j x => (presentation L M h).decode ((sourceSignatures L M h) j x))
      (fun j u v => (presentation L M h).decode ((targetTables L M h).edge j u v))).map
        (field L M h).subtype) = (sourceInput L M h G).val.realize (sourceInput L M h G).property
          (ambientSource L M h) (kernels .nativeX) := by
    unfold Holant.Network.map Holant.Complexity.RawClosedNetwork.realize
    congr 1
    · funext v x
      exact familyCoordinates_spec (values L M h) (algebraic L M h) _
    · funext e a b
      exact familyCoordinates_spec (values L M h) (algebraic L M h) _
  dsimp only [sourceTables]
  rw [hm]
  have hn := network_value .nativeX M G
  rw [show Paper2.Paper1Proved.kernels .nativeX =
    (fun _ : Fin 1 => Holant.Signature.disequality) from rfl] at hn ⊢
  rw [Holant.Complexity.UniversalPairReduction.Surgery.Choice.denote_eq_evaluate] at hn ⊢
  have tableEq : Holant.Complexity.UniversalPairReduction.Surgery.Choice.table (ambientSource L M h) =
      Holant.Complexity.UniversalPairReduction.Surgery.Choice.table (signatures M) := by
    funext label bits
    unfold Holant.Complexity.UniversalPairReduction.Surgery.Choice.table
    split_ifs with hi
    · simp [ambientSource,signatures]
    · rfl
  rw [tableEq]
  exact hn

 include h in
 theorem reduction : FixedFieldOutput.Reduces .nativeX M L := by
  let r := GadgetController.controlled (presentation L M h) (templates L M h) (wellFormed L M h)
    (targetTables L M h) (sourceSignatures L M h) (scales L M h) (scales_nonzero L M h) (macro_exact L M h)
  exact ⟨canonicalReduction .nativeX .nativeX M L
    (Holant.Complexity.RawClosedNetwork.validatedEncoding M.count 1 (sourceArity (templates L M h)))
    (presentation L M h) (embedding L M h) (sourceValue L M h) (sourceInput L M h)
    (inputComputes L M h) (source_correct L M h)
    (presentation L M h) (embedding L M h) Subtype.val_injective (targetValue L M h)
    (target_correct L M h) r⟩
end GadgetProvider

 theorem directGadgetProvider : SourceFaithful.Paper1DirectGadgetAccepted :=
  ⟨fun L M _ h => GadgetProvider.reduction L M h⟩
end
end Paper2.Paper1Proved
