import Paper2.CommonPhase.ZeroLoops
import Mathlib.Basic.Complex.Basic

/-!
# Recovering real complement symmetry from actual contraction tables

On EO tensors with at least three ports, the complete family of genuine
native-X pair contractions is injective. Applying that fact to imaginary
parts and complement differences recovers both properties of the input.
-/

namespace Paper2.CommonPhase

open EndpointSelfLoop

variable {ι : Type} {K L : Type*}

/-- Additive coefficient maps commute with the exact two-state contraction. -/
theorem loop_map [AddCommMonoid K] [AddCommMonoid L]
    (φ : K →+ L) (a b : ι) (hab : a ≠ b) (f : Tensor K ι)
    (y : Remaining a b → Bool) :
    loop a b hab (fun x => φ (f x)) y = φ (loop a b hab f y) := by
  change (∑ t : Bool, φ (f (extendPair a b hab y t))) =
    φ (∑ t : Bool, f (extendPair a b hab y t))
  exact (map_sum φ _ _).symm

/-- Taking the imaginary part retains every contraction summand. -/
theorem loop_im (a b : ι) (hab : a ≠ b) (f : Tensor ℂ ι)
    (y : Remaining a b → Bool) :
    loop a b hab (fun x => (f x).im) y = (loop a b hab f y).im :=
  loop_map Complex.imAddGroupHom a b hab f y

/-- Taking the real part retains every contraction summand. -/
theorem loop_re (a b : ι) (hab : a ≠ b) (f : Tensor ℂ ι)
    (y : Remaining a b → Bool) :
    loop a b hab (fun x => (f x).re) y = (loop a b hab f y).re :=
  loop_map Complex.reAddGroupHom a b hab f y

/-- Genuine native-X contraction is additive, hence preserves differences. -/
theorem loop_sub [AddCommGroup K] (a b : ι) (hab : a ≠ b)
    (f g : Tensor K ι) :
    loop a b hab (f - g) = loop a b hab f - loop a b hab g := by
  funext y
  change (∑ t : Bool, (f (extendPair a b hab y t) - g (extendPair a b hab y t))) =
    (∑ t : Bool, f (extendPair a b hab y t)) -
      (∑ t : Bool, g (extendPair a b hab y t))
  simp only [Finset.sum_sub_distrib]

/-- A difference remains in the common supported charge layer. -/
theorem chargeLayer_sub [Fintype ι] [AddGroup K]
    (f g : Tensor K ι) (c : ℤ)
    (hf : Tensor.ChargeLayer f c) (hg : Tensor.ChargeLayer g c) :
    Tensor.ChargeLayer (f - g) c := by
  intro x hx
  by_cases hfx : f x = 0
  · apply hg x
    intro hgx
    exact hx (by simp [hfx, hgx])
  · exact hf x hfx

/-- Complement preserves the zero-charge support layer. -/
theorem chargeLayer_zero_complement [Fintype ι] [Zero K]
    (f : Tensor K ι) (hf : Tensor.ChargeLayer f 0) :
    Tensor.ChargeLayer (fun x => f (fun i => !(x i))) 0 := by
  intro x hx
  have h := hf (fun i => !(x i)) hx
  rw [doubledCharge_complement] at h
  exact neg_eq_zero.mp h

/-- EO tensors of arity at least three are determined by their full family of
actual native-X pair contraction tables. -/
theorem eo_eq_of_pair_contractions_eq [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (hn : 3 ≤ Fintype.card ι)
    (f g : Tensor K ι) (hf : Tensor.ChargeLayer f 0) (hg : Tensor.ChargeLayer g 0)
    (heq : ∀ a b (hab : a ≠ b), loop a b hab f = loop a b hab g) : f = g := by
  apply sub_eq_zero.mp
  apply eo_zero_of_vanishing_pair_contractions h2 hn (f - g)
    (chargeLayer_sub f g 0 hf hg)
  intro a b hab
  rw [loop_sub, heq, sub_self]

/-- Reality of every actual contraction table forces reality of the EO input. -/
theorem eo_real_of_real_loops [Fintype ι] (hn : 3 ≤ Fintype.card ι)
    (f : Tensor ℂ ι) (hf : Tensor.ChargeLayer f 0)
    (hreal : ∀ a b (hab : a ≠ b) (y : Remaining a b → Bool),
      (loop a b hab f y).im = 0) :
    ∀ x, (f x).im = 0 := by
  have hg : Tensor.ChargeLayer (fun x => (f x).im) 0 := by
    intro x hx
    apply hf x
    intro hfx
    exact hx (by simp [hfx])
  have hz : (fun x => (f x).im) = (0 : Tensor ℝ ι) := by
    apply eo_zero_of_vanishing_pair_contractions (by norm_num) hn _ hg
    intro a b hab
    funext y
    exact (loop_im a b hab f y).trans (hreal a b hab y)
  intro x
  exact congrFun hz x

/-- Complement symmetry of every actual contraction table forces complement
symmetry of the EO input. No normalization of the tables is used. -/
theorem eo_complement_of_complement_loops [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (hn : 3 ≤ Fintype.card ι)
    (f : Tensor K ι) (hf : Tensor.ChargeLayer f 0)
    (hcomp : ∀ a b (hab : a ≠ b) (y : Remaining a b → Bool),
      loop a b hab f (fun i => !(y i)) = loop a b hab f y) :
    ∀ x, f (fun i => !(x i)) = f x := by
  have heq : (fun x => f (fun i => !(x i))) = f := by
    apply eo_eq_of_pair_contractions_eq h2 hn _ f
      (chargeLayer_zero_complement f hf) hf
    intro a b hab
    funext y
    exact (loop_complement a b hab f y).trans (hcomp a b hab y)
  intro x
  exact congrFun heq x

/-- Recovery of both properties for a complex EO coefficient table from its
actual matching deck. The only arity hypothesis is at least three ports. -/
theorem eo_real_complement_of_loops [Fintype ι] (hn : 3 ≤ Fintype.card ι)
    (f : Tensor ℂ ι) (hf : Tensor.ChargeLayer f 0)
    (hreal : ∀ a b (hab : a ≠ b) (y : Remaining a b → Bool),
      (loop a b hab f y).im = 0)
    (hcomp : ∀ a b (hab : a ≠ b) (y : Remaining a b → Bool),
      loop a b hab f (fun i => !(y i)) = loop a b hab f y) :
    (∀ x, (f x).im = 0) ∧ (∀ x, f (fun i => !(x i)) = f x) :=
  ⟨eo_real_of_real_loops hn f hf hreal,
    eo_complement_of_complement_loops (by norm_num) hn f hf hcomp⟩

end Paper2.CommonPhase
