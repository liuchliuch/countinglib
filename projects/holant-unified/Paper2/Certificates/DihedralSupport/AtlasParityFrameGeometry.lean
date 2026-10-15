import Paper2.Certificates.DihedralSupport.AtlasParityFrame
import Paper2.Certificates.DihedralSupport.AtlasGeometryCore
import Paper2.Certificates.DihedralSupport.CyclotomicArithmetic

/-! Exact geometry in the actual parity-word frame. Evaluation at the
literal frame words is a left inverse, so extending by zero preserves and
reflects linear relations and projective equality without a rank premise. -/
namespace Paper2.Certificates.DihedralSupport.AtlasParityFrame
open Paper2.HeightOne Paper2.HeightOne.Cyclic
open AtlasVectors AtlasGeometry
noncomputable section

variable {K : Type} [Field K]

theorem extendVector_injective (epsilon : Bool) :
    Function.Injective (extendVector (K := K) epsilon) := by
  intro u v h
  funext c
  have hc := congrFun h (word epsilon c)
  simpa only [extendVector_word] using hc

theorem extendVector_eq_iff (epsilon : Bool) (u v : Coordinate → K) :
    extendVector epsilon u = extendVector epsilon v ↔ u = v :=
  (extendVector_injective epsilon).eq_iff

theorem extendVector_zero (epsilon : Bool) :
    extendVector epsilon (0 : Coordinate → K) = 0 := by
  funext x
  simp [extendVector]

theorem extendVector_add (epsilon : Bool) (u v : Coordinate → K) :
    extendVector epsilon (u + v) = extendVector epsilon u + extendVector epsilon v := by
  funext x
  by_cases hp : parity x = epsilon.toNat <;> simp [extendVector, hp]

theorem extendVector_smul (epsilon : Bool) (c : K) (u : Coordinate → K) :
    extendVector epsilon (c • u) = c • extendVector epsilon u := by
  funext x
  by_cases hp : parity x = epsilon.toNat <;> simp [extendVector, hp]

def extendLinearMap (epsilon : Bool) : (Coordinate → K) →ₗ[K] Signature K 4 where
  toFun := extendVector epsilon
  map_add' := extendVector_add epsilon
  map_smul' := extendVector_smul epsilon

@[simp] theorem extendLinearMap_apply (epsilon : Bool) (u : Coordinate → K) :
    extendLinearMap epsilon u = extendVector epsilon u := rfl

theorem extendLinearMap_injective (epsilon : Bool) :
    Function.Injective (extendLinearMap (K := K) epsilon) := extendVector_injective epsilon

theorem extendVector_eq_zero_iff (epsilon : Bool) (u : Coordinate → K) :
    extendVector epsilon u = 0 ↔ u = 0 := by
  rw [← extendVector_zero epsilon]
  exact extendVector_eq_iff epsilon u 0

/-- Reflection also holds for the zero scalar. -/
theorem scalar_eq_extend_iff (epsilon : Bool) (c : K) (u v : Coordinate → K) :
    extendVector epsilon v = c • extendVector epsilon u ↔ v = c • u := by
  rw [← extendVector_smul epsilon]
  exact extendVector_eq_iff epsilon v (c • u)

theorem smul_eq_extend_iff (epsilon : Bool) (c : K) (u v : Coordinate → K) :
    c • extendVector epsilon u = extendVector epsilon v ↔ c • u = v := by
  rw [eq_comm, scalar_eq_extend_iff, eq_comm]

theorem proportional_extend_iff (epsilon : Bool) (u v : Coordinate → K) :
    CyclotomicArithmetic.Proportional (extendVector epsilon u) (extendVector epsilon v) ↔
      CyclotomicArithmetic.Proportional u v := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun a => ?_⟩
    simpa only [extendVector_word] using h (word epsilon a)
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun x => ?_⟩
    by_cases hp : parity x = epsilon.toNat
    · simpa [extendVector, hp] using h (coordinates x)
    · simp [extendVector, hp]

theorem onLine_extend_iff (epsilon : Bool) (u v w : Coordinate → K) :
    OnLine (extendVector epsilon u) (extendVector epsilon v) (extendVector epsilon w) ↔
      OnLine u v w := by
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a, b, ?_⟩
    apply extendVector_injective epsilon
    rw [extendVector_add, extendVector_smul, extendVector_smul]
    exact h
  · rintro ⟨a, b, h⟩
    refine ⟨a, b, ?_⟩
    rw [← extendVector_smul, ← extendVector_smul, ← extendVector_add, h]

theorem minor2_extend_word (epsilon : Bool) (u v : Coordinate → K) (a b : Coordinate) :
    minor2 (extendVector epsilon u) (extendVector epsilon v) (word epsilon a) (word epsilon b) =
      minor2 u v a b := by
  simp only [minor2, extendVector_word]

theorem minor3_extend_word (epsilon : Bool) (u v w : Coordinate → K) (a b c : Coordinate) :
    minor3 (extendVector epsilon u) (extendVector epsilon v) (extendVector epsilon w)
      (word epsilon a) (word epsilon b) (word epsilon c) = minor3 u v w a b c := by
  simp only [minor3, extendVector_word]

/-- Every minor outside the chosen parity frame vanishes exactly. -/
theorem minor3_extend (epsilon : Bool) (u v w : Coordinate → K) (x y z : Fin 4 → Bool) :
    minor3 (extendVector epsilon u) (extendVector epsilon v) (extendVector epsilon w) x y z =
      if parity x = epsilon.toNat ∧ parity y = epsilon.toNat ∧ parity z = epsilon.toNat
        then minor3 u v w (coordinates x) (coordinates y) (coordinates z) else 0 := by
  by_cases hx : parity x = epsilon.toNat <;>
    by_cases hy : parity y = epsilon.toNat <;>
    by_cases hz : parity z = epsilon.toNat <;> simp [minor3, extendVector, hx, hy, hz]

theorem zeroMinors_extend_iff (epsilon : Bool) (u v w : Coordinate → K) :
    ZeroMinors (extendVector epsilon u) (extendVector epsilon v) (extendVector epsilon w) ↔
      ZeroMinors u v w := by
  constructor
  · intro h a b c
    simpa only [minor3_extend_word] using h (word epsilon a) (word epsilon b) (word epsilon c)
  · intro h x y z
    rw [minor3_extend]
    split
    · exact h _ _ _
    · rfl

theorem table_eq_extendVector (omega : K) (epsilon : Bool) (l : AtlasCounts.PointLabel) :
    table omega epsilon l = extendVector epsilon (vector omega l) := rfl

theorem onLine_table_iff (omega : K) (epsilon : Bool) (l m n : AtlasCounts.PointLabel) :
    OnLine (table omega epsilon l) (table omega epsilon m) (table omega epsilon n) ↔
      OnLine (vector omega l) (vector omega m) (vector omega n) :=
  onLine_extend_iff epsilon _ _ _

theorem proportional_table_iff (omega : K) (epsilon : Bool) (l m : AtlasCounts.PointLabel) :
    CyclotomicArithmetic.Proportional (table omega epsilon l) (table omega epsilon m) ↔
      CyclotomicArithmetic.Proportional (vector omega l) (vector omega m) :=
  proportional_extend_iff epsilon _ _

end
end Paper2.Certificates.DihedralSupport.AtlasParityFrame

