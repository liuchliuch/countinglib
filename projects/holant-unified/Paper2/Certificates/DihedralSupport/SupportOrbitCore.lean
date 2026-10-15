module
public import Paper2.Certificates.DihedralSupport.Semantics
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Finset.Card

/-! Signed port permutations act on the actual six-bit words. The orbit
certificate below uses only this action, with a concrete six-point seed. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport.SupportOrbit

abbrev Word := Fin 6 → Bool

def sstarMask : Nat := 1 + 2^3 + 2^12 + 2^51 + 2^60 + 2^63

def sstar (x : Word) : Bool := sstarMask.testBit (index6 x)

def zeroWord : Word := fun _ => false

def wordAction (σ : Equiv.Perm (Fin 6)) (b x : Word) : Word :=
  fun i => (x (σ i)) ^^ (b i)

def maskAction (σ : Equiv.Perm (Fin 6)) (b : Word) (m : Nat) : Nat :=
  encodeSupport fun x => m.testBit (index6 (wordAction σ b x))

@[simp] theorem maskAction_spec (σ : Equiv.Perm (Fin 6)) (b x : Word) (m : Nat) :
    (maskAction σ b m).testBit (index6 x) =
      m.testBit (index6 (wordAction σ b x)) := encodeSupport_spec _ _

theorem maskAction_lt (σ : Equiv.Perm (Fin 6)) (b : Word) (m : Nat) :
    maskAction σ b m < 18446744073709551616 := encodeSupport_lt _

theorem encode_testBit (m : Nat) (hm : m < 18446744073709551616) :
    encodeSupport (fun x => m.testBit (index6 x)) = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [encodeSupport, testBit_packBits]
  by_cases hi : i < 64
  · simp [hi, index6_word6 ⟨i, hi⟩]
  · have hm' : m < 2^i := by
      calc
        m < 2^64 := hm
        _ ≤ 2^i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)
    simp [hi, Nat.testBit_eq_false_of_lt hm']

@[simp] theorem maskAction_one (m : Nat) (hm : m < 18446744073709551616) :
    maskAction 1 zeroWord m = m := by
  have hx (x : Word) : wordAction 1 zeroWord x = x := by
    funext i
    simp [wordAction, zeroWord]
  simpa only [maskAction, hx] using encode_testBit m hm

theorem maskAction_perm_comp (σ τ : Equiv.Perm (Fin 6)) (m : Nat) :
    maskAction σ zeroWord (maskAction τ zeroWord m) =
      maskAction (σ * τ) zeroWord m := by
  unfold maskAction
  congr 1
  funext x
  rw [encodeSupport_spec]
  have hx : wordAction τ zeroWord (wordAction σ zeroWord x) =
      wordAction (σ * τ) zeroWord x := by
    funext i
    simp [wordAction, zeroWord, Equiv.Perm.mul_apply]
  rw [hx]

def singleFlip (i : Fin 6) : Word := fun j => decide (j = i)
def flips (s : Finset (Fin 6)) : Word := fun j => decide (j ∈ s)

theorem maskAction_flips_insert (i : Fin 6) (s : Finset (Fin 6)) (hi : i ∉ s) (m : Nat) :
    maskAction 1 (flips (insert i s)) m =
      maskAction 1 (singleFlip i) (maskAction 1 (flips s) m) := by
  unfold maskAction
  congr 1
  funext x
  rw [encodeSupport_spec]
  congr 2
  funext j
  by_cases hji : j = i
  · subst j
    simp [wordAction, singleFlip, flips, hi]
  · simp [wordAction, singleFlip, flips, hji]

theorem maskAction_perm_flip (σ : Equiv.Perm (Fin 6)) (b : Word) (m : Nat) :
    maskAction σ zeroWord (maskAction 1 b m) = maskAction σ b m := by
  unfold maskAction
  congr 1
  funext x
  rw [encodeSupport_spec]
  have hx : wordAction 1 b (wordAction σ zeroWord x) = wordAction σ b x := by
    funext i
    simp [wordAction, zeroWord]
  rw [hx]

def wordEquiv (σ : Equiv.Perm (Fin 6)) (b : Word) : Word ≃ Word where
  toFun := wordAction σ b
  invFun := fun x i => (x (σ.symm i)) ^^ (b (σ.symm i))
  left_inv := by
    intro x
    funext i
    simp [wordAction]
  right_inv := by
    intro x
    funext i
    simp [wordAction]

def xor3 (x y z : Word) : Word := fun i => (x i) ^^ ((y i) ^^ (z i))
def XorClosed (S : Word → Bool) : Prop :=
  ∀ x y z, S x = true → S y = true → S z = true → S (xor3 x y z) = true

theorem wordAction_xor3 (σ : Equiv.Perm (Fin 6)) (b x y z : Word) :
    wordAction σ b (xor3 x y z) =
      xor3 (wordAction σ b x) (wordAction σ b y) (wordAction σ b z) := by
  funext i
  simp only [wordAction, xor3]
  cases x (σ i) <;> cases y (σ i) <;> cases z (σ i) <;> cases b i <;> rfl

private theorem seed_bad : sstar (word6 0) = true ∧ sstar (word6 3) = true ∧
    sstar (word6 12) = true ∧ sstar (xor3 (word6 0) (word6 3) (word6 12)) = false := by
  decide +kernel

theorem signed_seed_not_xorClosed (σ : Equiv.Perm (Fin 6)) (b : Word) :
    ¬ XorClosed (fun x => sstar (wordAction σ b x)) := by
  intro h
  let e := wordEquiv σ b
  have he (x : Word) : wordAction σ b (e.symm x) = x := e.apply_symm_apply x
  have hx := h (e.symm (word6 0)) (e.symm (word6 3)) (e.symm (word6 12))
    (by simpa only [he] using seed_bad.1)
    (by simpa only [he] using seed_bad.2.1)
    (by simpa only [he] using seed_bad.2.2.1)
  change sstar (wordAction σ b
    (xor3 (e.symm (word6 0)) (e.symm (word6 3)) (e.symm (word6 12)))) = true at hx
  rw [wordAction_xor3, he, he, he, seed_bad.2.2.2] at hx
  cases hx

end Paper2.Certificates.DihedralSupport.SupportOrbit
