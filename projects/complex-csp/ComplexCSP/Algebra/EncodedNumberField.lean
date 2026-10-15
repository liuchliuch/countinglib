import Mathlib.RingTheory.PowerBasis
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

/-! # Runtime rational-vector arithmetic from an input monic relation

The executable definitions use only a dimension and rational coefficient vectors.
Their correctness is interpreted against a separately supplied algebraic root;
a power basis is used only to prove uniqueness and reflect equality. This module
does not construct or validate a power basis from arbitrary input encodings.
-/
namespace ComplexCSP.EncodedNumberField
open scoped BigOperators

/-- Runtime coordinates, indexed by powers from zero through `n - 1`. -/
abbrev CoeffVector (n : ℕ) := Fin n → ℚ

def zero (n : ℕ) : CoeffVector n := fun _ => 0

def add {n : ℕ} (a b : CoeffVector n) : CoeffVector n := fun i => a i + b i

def neg {n : ℕ} (a : CoeffVector n) : CoeffVector n := fun i => -a i

def one (n : ℕ) : CoeffVector n := fun i => if i.val = 0 then 1 else 0

def unitVector {n : ℕ} (j : Fin n) : CoeffVector n := fun i => if i = j then 1 else 0

/-- Exact rational coordinate comparison, using only finite enumeration. -/
def equal {n : ℕ} (a b : CoeffVector n) : Bool := decide (∀ i, a i = b i)

@[simp] theorem equal_correct {n : ℕ} (a b : CoeffVector n) :
    equal a b = true ↔ a = b := by simp [equal, funext_iff]

/-- Multiply a basis monomial by the generator, reducing the top power using c. -/
def shiftedMonomial {n : ℕ} (c : CoeffVector n) (j : Fin n) : CoeffVector n :=
  if h : j.val + 1 < n then unitVector ⟨j.val + 1, h⟩ else c

/-- Executable multiplication by α under the input relation α^n = Σ cᵢ α^i. -/
def shift {n : ℕ} (c a : CoeffVector n) : CoeffVector n :=
  ∑ j, a j • shiftedMonomial c j

/-- A bounded iteration of the executable shift. -/
def shiftPower {n : ℕ} (c : CoeffVector n) (a : CoeffVector n) : ℕ → CoeffVector n
  | 0 => a
  | k + 1 => shift c (shiftPower c a k)

/-- Multiply by finite linear combination of generator-shifted copies. -/
def mul {n : ℕ} (c a b : CoeffVector n) : CoeffVector n :=
  ∑ j, b j • shiftPower c a j.val

/-- Natural powers; all recursion is bounded by the supplied exponent. -/
def pow {n : ℕ} (c a : CoeffVector n) : ℕ → CoeffVector n
  | 0 => one n
  | k + 1 => mul c (pow c a k) a

/-- Polynomial substitution, used for an input conjugate-generator vector. -/
def substitute {n : ℕ} (c b a : CoeffVector n) : CoeffVector n :=
  ∑ j, a j • pow c b j.val

section Interpretation
variable {K : Type*} [CommRing K] [Algebra ℚ K] {n : ℕ}

/-- Proof-level interpretation of runtime coordinates at an actual generator. -/
def interpret (α : K) (a : CoeffVector n) : K :=
  ∑ i, algebraMap ℚ K (a i) * α ^ i.val

@[simp] theorem interpret_zero (α : K) : interpret α (zero n) = 0 := by
  simp [interpret, zero]

@[simp] theorem interpret_add (α : K) (a b : CoeffVector n) :
    interpret α (add a b) = interpret α a + interpret α b := by
  simp [interpret, add, add_mul, Finset.sum_add_distrib]

@[simp] theorem interpret_neg (α : K) (a : CoeffVector n) :
    interpret α (neg a) = -interpret α a := by simp [interpret, neg]

@[simp] theorem interpret_smul (α : K) (q : ℚ) (a : CoeffVector n) :
    interpret α (q • a) = algebraMap ℚ K q * interpret α a := by
  simp [interpret, Finset.mul_sum, mul_assoc]

@[simp] theorem interpret_sum (α : K) {J : Type*} (s : Finset J) (a : J → CoeffVector n) :
    interpret α (∑ j ∈ s, a j) = ∑ j ∈ s, interpret α (a j) := by
  simp only [interpret, Finset.sum_apply, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

@[simp] theorem interpret_unitVector (α : K) (j : Fin n) :
    interpret α (unitVector j) = α ^ j.val := by
  classical
  simp [interpret, unitVector]

@[simp] theorem interpret_one (α : K) (hn : 0 < n) : interpret α (one n) = 1 := by
  have he : one n = unitVector (⟨0,hn⟩ : Fin n) := by
    funext i
    simp [one, unitVector, Fin.ext_iff]
  rw [he, interpret_unitVector]
  simp

/-- The only reduction validity obligation is the actual monic root equation. -/
theorem interpret_shiftedMonomial (α : K) (c : CoeffVector n)
    (hc : α ^ n = interpret α c) (j : Fin n) :
    interpret α (shiftedMonomial c j) = α ^ (j.val + 1) := by
  unfold shiftedMonomial
  split_ifs with h
  · exact interpret_unitVector α _
  · have hj : j.val + 1 = n := by omega
    rw [hj, hc]

theorem interpret_shift (α : K) (c a : CoeffVector n)
    (hc : α ^ n = interpret α c) : interpret α (shift c a) = α * interpret α a := by
  unfold shift
  rw [interpret_sum]
  simp only [interpret_smul, interpret_shiftedMonomial α c hc, pow_succ]
  simp only [interpret, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem interpret_shiftPower (α : K) (c a : CoeffVector n)
    (hc : α ^ n = interpret α c) (k : ℕ) :
    interpret α (shiftPower c a k) = α ^ k * interpret α a := by
  induction k with
  | zero => simp [shiftPower]
  | succ k ih =>
    rw [shiftPower, interpret_shift α c _ hc, ih, pow_succ]
    ring

theorem interpret_mul (α : K) (c a b : CoeffVector n)
    (hc : α ^ n = interpret α c) :
    interpret α (mul c a b) = interpret α a * interpret α b := by
  unfold mul
  rw [interpret_sum]
  simp only [interpret_smul, interpret_shiftPower α c a hc]
  change (∑ j, algebraMap ℚ K (b j) * (α ^ j.val * interpret α a)) =
    interpret α a * (∑ j, algebraMap ℚ K (b j) * α ^ j.val)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem interpret_pow (α : K) (c a : CoeffVector n) (hn : 0 < n)
    (hc : α ^ n = interpret α c) (k : ℕ) :
    interpret α (pow c a k) = interpret α a ^ k := by
  induction k with
  | zero => simpa only [pow, pow_zero] using interpret_one α hn
  | succ k ih => rw [pow, interpret_mul α c _ a hc, ih, pow_succ]

theorem interpret_substitute (α : K) (c b a : CoeffVector n) (hn : 0 < n)
    (hc : α ^ n = interpret α c) :
    interpret α (substitute c b a) = interpret (interpret α b) a := by
  unfold substitute
  rw [interpret_sum]
  change (∑ j, interpret α (a j • pow c b j.val)) =
    ∑ j, algebraMap ℚ K (a j) * interpret α b ^ j.val
  simp only [interpret_smul, interpret_pow α c b hn hc]

end Interpretation

section PowerBasis
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Coordinate interpretation is injective because the indicated powers are an
actual basis. The basis is not used by any arithmetic routine. -/
theorem interpret_injective (pb : PowerBasis ℚ K) :
    Function.Injective (interpret pb.gen : CoeffVector pb.dim → K) := by
  intro a b hab
  have he (v : CoeffVector pb.dim) : interpret pb.gen v = ∑ i, v i • pb.basis i := by
    simp only [interpret, pb.basis_eq_pow, Algebra.smul_def]
  simp only [he] at hab
  exact Fintype.linearIndependent_iff.mp pb.basis.linearIndependent (fun i => a i - b i)
    (by simpa [sub_smul, Finset.sum_sub_distrib] using sub_eq_zero.mpr hab) |>
      fun h => funext (fun i => sub_eq_zero.mp (h i))

/-- The supplied power-basis coordinates reconstruct their actual field value. -/
theorem interpret_coordinates (pb : PowerBasis ℚ K) (z : K) :
    interpret pb.gen (pb.basis.equivFun z) = z := by
  simpa only [interpret, pb.basis_eq_pow, Algebra.smul_def] using pb.basis.sum_equivFun z

/-- Interpreting any coordinate vector and extracting the basis coefficients is
exactly the original vector. This extraction appears only in semantic proofs. -/
theorem coordinates_interpret (pb : PowerBasis ℚ K) (a : CoeffVector pb.dim) :
    pb.basis.equivFun (interpret pb.gen a) = a := by
  apply interpret_injective pb
  exact interpret_coordinates pb _

/-- Executable comparison is exact semantic equality, with no classical equality
procedure on the target field installed in the runtime code. -/
theorem equal_iff_interpret (pb : PowerBasis ℚ K) (a b : CoeffVector pb.dim) :
    equal a b = true ↔ interpret pb.gen a = interpret pb.gen b :=
  (equal_correct a b).trans (interpret_injective pb).eq_iff.symm
end PowerBasis

/-- A supplied rational vector for the conjugate generator gives executable
conjugation by substitution. Its semantic validity is an explicit input check. -/
theorem interpret_conjugate {n : ℕ} (α : ℂ) (c b a : CoeffVector n) (hn : 0 < n)
    (hc : α ^ n = interpret α c) (hb : interpret α b = star α) :
    interpret α (substitute c b a) = star (interpret α a) := by
  rw [interpret_substitute α c b a hn hc, hb]
  simp [interpret, star_sum, star_mul, star_pow, mul_comm]

end ComplexCSP.EncodedNumberField
