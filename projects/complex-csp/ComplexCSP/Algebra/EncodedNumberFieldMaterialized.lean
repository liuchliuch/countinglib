import ComplexCSP.Algebra.EncodedNumberFieldInverse

/-! # Materialized runtime rational-vector recursion

Recursive shift and power state is actual finite Vector data. A getter is exposed
only at the public function boundary; an optimizer cannot turn the recursive
state into a repeatedly expanded function expression. Extensional equalities
preserve every previously verified arithmetic specification.
-/
namespace ComplexCSP.EncodedNumberField
open scoped BigOperators

def vectorView {n : ℕ} (v : Vector ℚ n) : CoeffVector n := fun i => v.get i

@[simp] theorem vectorView_ofFn {n : ℕ} (a : CoeffVector n) :
    vectorView (Vector.ofFn a) = a := funext (fun i => Vector.getElem_ofFn i.isLt)

def materialize {n : ℕ} (a : CoeffVector n) : CoeffVector n := vectorView (Vector.ofFn a)
@[simp] theorem materialize_eq {n : ℕ} (a : CoeffVector n) : materialize a = a := vectorView_ofFn a
@[simp] theorem materialize_apply {n : ℕ} (a : CoeffVector n) (i : Fin n) :
    materialize a i = a i := congrFun (materialize_eq a) i

/-- Crucially, the recursive state has a data-valued codomain. -/
def shiftVector {n : ℕ} (c a : CoeffVector n) : ℕ → Vector ℚ n
  | 0 => Vector.ofFn a
  | k + 1 => Vector.ofFn (shift c (vectorView (shiftVector c a k)))

@[simp] theorem shiftVector_view {n : ℕ} (c a : CoeffVector n) (k : ℕ) :
    vectorView (shiftVector c a k) = shiftPower c a k := by
  induction k with
  | zero => simp only [shiftVector, vectorView_ofFn, shiftPower]
  | succ k ih => simp only [shiftVector, vectorView_ofFn, ih, shiftPower]

def materializedShiftPower {n : ℕ} (c a : CoeffVector n) (k : ℕ) : CoeffVector n :=
  vectorView (shiftVector c a k)

@[simp] theorem materializedShiftPower_eq {n : ℕ} (c a : CoeffVector n) (k : ℕ) :
    materializedShiftPower c a k = shiftPower c a k := shiftVector_view c a k

def productVector {n : ℕ} (c a b : CoeffVector n) : Vector ℚ n :=
  Vector.ofFn (∑ j, b j • vectorView (shiftVector c a j.val))

@[simp] theorem productVector_view {n : ℕ} (c a b : CoeffVector n) :
    vectorView (productVector c a b) = mul c a b := by
  simp only [productVector, vectorView_ofFn, shiftVector_view, mul]

def materializedMul {n : ℕ} (c a b : CoeffVector n) : CoeffVector n :=
  vectorView (productVector c a b)

@[simp] theorem materializedMul_eq {n : ℕ} (c a b : CoeffVector n) :
    materializedMul c a b = mul c a b := productVector_view c a b

/-- Powers retain every previous result as finite data rather than as a function. -/
def powerVector {n : ℕ} (c a : CoeffVector n) : ℕ → Vector ℚ n
  | 0 => Vector.ofFn (one n)
  | k + 1 => productVector c (vectorView (powerVector c a k)) a

@[simp] theorem powerVector_view {n : ℕ} (c a : CoeffVector n) (k : ℕ) :
    vectorView (powerVector c a k) = pow c a k := by
  induction k with
  | zero => simp only [powerVector, vectorView_ofFn, pow]
  | succ k ih => simp only [powerVector, productVector_view, ih, pow]

def materializedPow {n : ℕ} (c a : CoeffVector n) (k : ℕ) : CoeffVector n :=
  vectorView (powerVector c a k)

@[simp] theorem materializedPow_eq {n : ℕ} (c a : CoeffVector n) (k : ℕ) :
    materializedPow c a k = pow c a k := powerVector_view c a k

def inverseVector {n : ℕ} (c a : CoeffVector n) : Vector ℚ n :=
  Vector.ofFn (if equal a (zero n) then zero n else
    (EffectiveRoots.rationalInverse
      (fun i j => materializedMul c a (unitVector j) i)).mulVec (one n))

def materializedInverse {n : ℕ} (c a : CoeffVector n) : CoeffVector n :=
  vectorView (inverseVector c a)

@[simp] theorem materializedInverse_eq {n : ℕ} (c a : CoeffVector n) :
    materializedInverse c a = inverse c a := by
  simp only [materializedInverse, inverseVector, vectorView_ofFn, materializedMul_eq]
  rfl

end ComplexCSP.EncodedNumberField
