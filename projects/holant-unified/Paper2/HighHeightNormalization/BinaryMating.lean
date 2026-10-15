import Paper2.MatchingPropagation

/-! Exact HN.2/HN.3 identities, with every native-X bit sum retained. -/
namespace Paper2.HighHeightNormalization
open MatchingPropagation CommonPhase EndpointSelfLoop
variable {ι : Type}

/-- The source's ordered ARS binary B(z). -/
def binary (z : ℂ) : Kernel ℂ := WeightedMatching.binary z (star z)

def matingWeight (z : ℂ) (b : Bool) : ℂ := if b then z else star z

/-- Attaching the first port of B(z) through X acts by B(z)ᵀ X. -/
def mating (z : ℂ) : Kernel ℂ :=
  Kernel.mul (Kernel.transpose (binary z)) Signature.disequality

@[simp] theorem mating_apply (z : ℂ) (a b : Bool) :
    mating z a b = if a = b then matingWeight z a else 0 := by
  cases a <;> cases b <;>
    simp [mating,Kernel.mul,Kernel.transpose,binary,WeightedMatching.binary,
      Signature.disequality,matingWeight]

theorem matingWeight_ne_zero {z : ℂ} (hz : z ≠ 0) (b : Bool) :
    matingWeight z b ≠ 0 := by
  cases b <;> simpa [matingWeight] using hz

/-- The complete ordered table identity T_z B(z) = z·conj(z) X. -/
theorem mating_binary (z : ℂ) :
    Kernel.mul (mating z) (binary z) =
      fun a b => (z * star z) * Signature.disequality a b := by
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.mul,binary,WeightedMatching.binary,matingWeight,Signature.disequality,mul_comm]

/-- The diagonal action has an explicit two-sided inverse whenever z is nonzero. -/
theorem mating_inverse {z : ℂ} (hz : z ≠ 0) :
    Kernel.mul (mating z) (mating z⁻¹) = Signature.equality ∧
      Kernel.mul (mating z⁻¹) (mating z) = Signature.equality := by
  constructor <;> funext a b <;> cases a <;> cases b <;>
    simp [Kernel.mul,matingWeight,Signature.equality,hz]

/-- HN.3's splice, with the two actual off-diagonal coefficients displayed. -/
theorem binary_splice (z w : ℂ) :
    Kernel.mul (Kernel.mul (Kernel.transpose (binary z)) Signature.disequality) (binary w) =
      WeightedMatching.binary (star z * w) (z * star w) := by
  change Kernel.mul (mating z) (binary w) = _
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.mul,binary,WeightedMatching.binary,matingWeight]

/-- Projective literal-X means a retained nonzero scalar, not just matching support. -/
def ScalarX (A : Kernel ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ A = fun a b => c * Signature.disequality a b

theorem binary_scalarX_iff {p q : ℂ} (hp : p ≠ 0) :
    ScalarX (WeightedMatching.binary p q) ↔ p = q := by
  constructor
  · rintro ⟨c,hc,he⟩
    have h₁ := congrFun (congrFun he false) true
    have h₂ := congrFun (congrFun he true) false
    simp [WeightedMatching.binary,Signature.disequality] at h₁ h₂
    exact h₁.trans h₂.symm
  · intro h
    refine ⟨p,hp,?_⟩
    funext a b
    cases a <;> cases b <;> simp [WeightedMatching.binary,Signature.disequality,h]

theorem splice_scalarX_iff {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    ScalarX (Kernel.mul (Kernel.mul (Kernel.transpose (binary z)) Signature.disequality) (binary w)) ↔
      star z * w = z * star w := by
  rw [binary_splice]
  exact binary_scalarX_iff (mul_ne_zero (by simpa using hz) hw)

/-- HN.3's real ratio criterion, without presupposing proportional factors. -/
theorem splice_real_ratio_iff {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    ScalarX (Kernel.mul (Kernel.mul (Kernel.transpose (binary z)) Signature.disequality) (binary w)) ↔
      (w / z).im = 0 := by
  rw [splice_scalarX_iff hz hw, ← Complex.conj_eq_iff_im]
  change star z * w = z * star w ↔ star (w / z) = w / z
  rw [star_div₀,div_eq_div_iff (by simpa using hz) hz]
  constructor <;> intro h <;> simpa [mul_comm] using h.symm

/-- In the same orientations, the normalized ports preserve the X closing
kernel exactly when the binary splice is scalar X. -/
theorem effective_kernel_scalarX {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (h : ScalarX (Kernel.mul (Kernel.mul (Kernel.transpose (binary z)) Signature.disequality) (binary w))) :
    ScalarX (Kernel.mul (Kernel.mul (Kernel.transpose (mating z)) Signature.disequality) (mating w)) := by
  have he := (splice_scalarX_iff hz hw).mp h
  refine ⟨star z * w,mul_ne_zero (by simpa using hz) hw,?_⟩
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.mul,Kernel.transpose,matingWeight,Signature.disequality]
  exact he.symm

/-- Actual one-port attachment of an ordered binary through native X. The old
mountain bit and the attached binary's first bit are both summed explicitly. -/
noncomputable def attach (a : ι) (B : Kernel ℂ) (F : Tensor ℂ ι) : Tensor ℂ ι := by
  classical
  exact fun x => ∑ u : Bool, ∑ v : Bool,
    F (Function.update x a u) * Signature.disequality u v * B v (x a)

/-- HN.2 at the full coefficient-table level, not merely as a matrix mnemonic. -/
theorem attach_binary (a : ι) (z : ℂ) (F : Tensor ℂ ι) (x : ι → Bool) :
    attach a (binary z) F x = matingWeight z (x a) * F x := by
  classical
  have hu : Function.update x a (x a) = x := by
    funext i
    by_cases hi : i = a <;> simp [Function.update,hi]
  simp only [attach,Fintype.sum_bool]
  cases hx : x a
  · have hu₀ : Function.update x a false = x := by simpa [hx] using hu
    simp [binary,WeightedMatching.binary,Signature.disequality,matingWeight,hx,hu₀,mul_comm]
  · have hu₁ : Function.update x a true = x := by simpa [hx] using hu
    simp [binary,WeightedMatching.binary,Signature.disequality,matingWeight,hx,hu₁,mul_comm]

theorem attach_binary_support (a : ι) (z : ℂ) (hz : z ≠ 0)
    (F : Tensor ℂ ι) (x : ι → Bool) : attach a (binary z) F x ≠ 0 ↔ F x ≠ 0 := by
  rw [attach_binary]
  simp [matingWeight_ne_zero hz _]

theorem attach_binary_chargeLayer [Fintype ι] (a : ι) (z : ℂ)
    (F : Tensor ℂ ι) (k : ℤ) (h : Tensor.ChargeLayer F k) :
    Tensor.ChargeLayer (attach a (binary z) F) k := by
  intro x hx
  apply h x
  intro hz
  apply hx
  rw [attach_binary,hz,mul_zero]

end Paper2.HighHeightNormalization
