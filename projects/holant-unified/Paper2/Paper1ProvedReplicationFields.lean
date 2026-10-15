import Paper2.Paper1ProvedReplicationGraphs
import Paper2.Paper1ProvedReplicationSemantics
import Paper2.Paper1ProvedReplicationPartition

/-! One actual number field contains both designated tables and the carrier
context's scalar. The literal copying graph retains its fixed nonzero closure
factor, and every field value embeds into the original native-X partition. -/
namespace Paper2.Paper1Proved.ReplicationFields
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
open Holant.Algebraic Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open Holant.LocalDrafts.Hardness
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
variable (L : Language) {r s : ℕ}
variable (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s)
variable (C : CarrierContext L g h) (Z : NonzeroTaggedClosure L g)

abbrev Index := ExactSignatureTables.CoefficientIndex (tagged L g).count 1 (tagged L g).arity ⊕
  (ExactSignatureTables.CoefficientIndex (tagged L h).count 1 (tagged L h).arity ⊕ Unit)

def values : Index L g h → AlgebraicComplex
  | .inl (.inl ⟨i,x⟩) => (tagged L g).signature i x
  | .inl (.inr (_,a,b)) => Signature.disequality a b
  | .inr (.inl (.inl ⟨i,x⟩)) => (tagged L h).signature i x
  | .inr (.inl (.inr (_,a,b))) => Signature.disequality a b
  | .inr (.inr _) => C.scalar

theorem algebraic (j : Index L g h) : IsAlgebraic ℚ (values L g h C j) :=
  Algebra.IsAlgebraic.isAlgebraic _
abbrev field := familyField (values L g h C)
abbrev presentation := familyPresentation (values L g h C) (algebraic L g h C)
def embedding : field L g h C →ₗ[ℚ] AlgebraicComplex := (field L g h C).val.toLinearMap

def scale : field L g h C := fieldCoefficient (values L g h C) (.inr (.inr ()))
theorem scale_correct : (scale L g h C : AlgebraicComplex)=C.scalar := rfl
theorem scale_nonzero : scale L g h C≠0 := by
  intro hz
  exact C.scalar_ne_zero (congrArg Subtype.val hz)

def targetTables : ExactSignatureTables (Module.finrank ℚ (field L g h C))
    (tagged L g).count 1 (tagged L g).arity where
  vertex i x := familyCoordinates (values L g h C) (algebraic L g h C) (.inl (.inl ⟨i,x⟩))
  edge i a b := familyCoordinates (values L g h C) (algebraic L g h C) (.inl (.inr (i,a,b)))

def sourceTables : ExactSignatureTables (Module.finrank ℚ (field L g h C))
    (tagged L h).count 1 (tagged L h).arity where
  vertex i x := familyCoordinates (values L g h C) (algebraic L g h C) (.inr (.inl (.inl ⟨i,x⟩)))
  edge i a b := familyCoordinates (values L g h C) (algebraic L g h C) (.inr (.inl (.inr (i,a,b))))

def sourceOldInput (x : ReplicationCompiler.Input (ReplicationGraphs.data L g h Z)) :
    SourceInput (tagged L h) := ⟨x.val,by rw [← ReplicationGraphs.sourceArity L g h Z]; exact x.property⟩

abbrev sourceValue (x : ReplicationCompiler.Input (ReplicationGraphs.data L g h Z)) : field L g h C :=
  (sourceTables L g h C).evaluate (presentation L g h C) (sourceOldInput L g h Z x)
abbrev targetValue (q : ReplicationGraphs.MarkedInput L g) : field L g h C :=
  (targetTables L g h C).evaluate (presentation L g h C) q.val
abbrev closureValue : field L g h C :=
  (targetTables L g h C).evaluate (presentation L g h C) (ReplicationGraphs.oldClosure L g Z)

private theorem target_cast (q : SourceInput (tagged L g)) :
    (((targetTables L g h C).evaluate (presentation L g h C) q : field L g h C) : AlgebraicComplex) =
      (q.val.realize q.property (signatures (tagged L g)) (kernels .nativeX)).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change (field L g h C).subtype _ = _
  rw [← Holant.Network.denote_map (field L g h C).subtype]
  congr 1
  unfold Holant.Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    exact familyCoordinates_spec (values L g h C) (algebraic L g h C) _
  · funext e a b
    exact familyCoordinates_spec (values L g h C) (algebraic L g h C) _

private theorem source_cast (x : ReplicationCompiler.Input (ReplicationGraphs.data L g h Z)) :
    (sourceValue L g h C Z x : AlgebraicComplex) =
      ((sourceOldInput L g h Z x).val.realize (sourceOldInput L g h Z x).property
        (signatures (tagged L h)) (kernels .nativeX)).denote Fin.elim0 := by
  rw [sourceValue,ExactSignatureTables.evaluate_eq_decoded]
  change (field L g h C).subtype _ = _
  rw [← Holant.Network.denote_map (field L g h C).subtype]
  congr 1
  unfold Holant.Network.map RawClosedNetwork.realize
  congr 1
  · funext v y
    exact familyCoordinates_spec (values L g h C) (algebraic L g h C) _
  · funext e a b
    exact familyCoordinates_spec (values L g h C) (algebraic L g h C) _

theorem target_correct (q : ReplicationGraphs.MarkedInput L g) :
    embedding L g h C (targetValue L g h C q) =
      Problem.value .nativeX (tagged L g) (ReplicationGraphs.canonicalTargetInput L g q).val := by
  change (targetValue L g h C q : AlgebraicComplex)=_
  rw [targetValue,target_cast]
  have hv := network_value .nativeX (tagged L g) ((inputIso (tagged L g)).symm q.val)
  change (((inputIso (tagged L g)) ((inputIso (tagged L g)).symm q.val)).val.realize
    (((inputIso (tagged L g)) ((inputIso (tagged L g)).symm q.val)).property)
      (signatures (tagged L g)) (kernels .nativeX)).denote Fin.elim0=_ at hv
  rwa [Equiv.apply_symm_apply] at hv

theorem source_correct (G : Instance (tagged L h)) :
    embedding L g h C (sourceValue L g h C Z (ReplicationGraphs.sourceInput L g h Z G)) =
      Problem.value .nativeX (tagged L h) G := by
  change (sourceValue L g h C Z (ReplicationGraphs.sourceInput L g h Z G) : AlgebraicComplex)=_
  rw [source_cast]
  exact network_value .nativeX (tagged L h) G

theorem closure_correct : (closureValue L g h C Z : AlgebraicComplex)=
    Problem.value .nativeX (tagged L g) Z.closedInput.val := by
  rw [closureValue,target_cast]
  exact network_value .nativeX (tagged L g) Z.closedInput.val

theorem closure_nonzero : closureValue L g h C Z≠0 := by
  intro hz
  apply Z.value_ne_zero
  rw [← closure_correct L g h C Z]
  exact congrArg Subtype.val hz



/-- The real physically substituted query obeys the exact carrier partition
identity inside the common field used by its executed oracle controller. -/
theorem partition (x : ReplicationCompiler.Input (ReplicationGraphs.data L g h Z)) :
    targetValue L g h C (ReplicationGraphs.query L g h C Z x) =
      (scale L g h C)^ReplicationCompiler.count x.val.vertices *
        closureValue L g h C Z * sourceValue L g h C Z x := by
  apply Subtype.ext
  change (field L g h C).subtype (targetValue L g h C (ReplicationGraphs.query L g h C Z x)) =
    (field L g h C).subtype ((scale L g h C)^ReplicationCompiler.count x.val.vertices *
      closureValue L g h C Z * sourceValue L g h C Z x)
  simp only [map_mul,map_pow]
  change (targetValue L g h C (ReplicationGraphs.query L g h C Z x) : AlgebraicComplex) =
    (scale L g h C : AlgebraicComplex)^ReplicationCompiler.count x.val.vertices *
      (closureValue L g h C Z : AlgebraicComplex) * (sourceValue L g h C Z x : AlgebraicComplex)
  rw [scale_correct,targetValue,target_cast,closureValue,target_cast,source_cast]
  exact ReplicationPartition.physical_partition L g h C Z x

def targetBound : PolynomialOutputBound (ReplicationGraphs.markedEncoding L g)
    (presentation L g h C).encoding (targetValue L g h C) where
  bound := (targetTables L g h C).outputPolynomial (presentation L g h C)
  length_le q := (targetTables L g h C).output_length_le (presentation L g h C) q.val

end
end Paper2.Paper1Proved.ReplicationFields
