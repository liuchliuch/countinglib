import Paper2.Kernel
import Mathlib.Tactic.NormNum

/-!
The ordered Bell dictionary of §2 and the local identities used in §8.
The real skew matrix `Y` here has entries (0,1,-1,0), not the physics
convention for the complex Pauli Y matrix. Every port order is explicit.
-/
namespace Paper2.Bell

variable {K : Type*} [Ring K]

/-- The phase (-1)^b, in an arbitrary ring. -/
def sign (b : Bool) : K := if b then -1 else 1

/-- B_{d,l}(u,v) = [u xor v = d] (-1)^(l u). -/
def ordered (d l : Bool) : Kernel K :=
  fun u v => if Bool.xor u v = d then sign (l && u) else 0

def I : Kernel K := ordered false false
def Z : Kernel K := ordered false true
def X : Kernel K := ordered true false
def Y : Kernel K := ordered true true

/-- A binary kernel's truth table in the fixed order 00,01,10,11. -/
def table (B : Kernel K) : Fin 4 → K :=
  ![B false false, B false true, B true false, B true true]

theorem table_I : table (I (K := K)) = ![1, 0, 0, 1] := rfl
theorem table_Z : table (Z (K := K)) = ![1, 0, 0, -1] := rfl
theorem table_X : table (X (K := K)) = ![0, 1, 1, 0] := rfl
theorem table_Y : table (Y (K := K)) = ![0, 1, -1, 0] := rfl

@[simp] theorem I_eq_equality : I (K := K) = Signature.equality := by
  funext u v
  cases u <;> cases v <;> rfl

@[simp] theorem X_eq_disequality : X (K := K) = Signature.disequality := by
  funext u v
  cases u <;> cases v <;> rfl

/-- Reversal contributes the sign (-1)^(d l); in particular Y is skew. -/
theorem ordered_reverse (d l u v : Bool) :
    ordered (K := K) d l v u = sign (d && l) * ordered d l u v := by
  cases d <;> cases l <;> cases u <;> cases v <;> simp [ordered, sign]

theorem transpose_Y : Kernel.transpose (Y (K := K)) = -Y := by
  funext u v
  cases u <;> cases v <;> simp [Kernel.transpose, Y, ordered, sign]

theorem complement_both (d l u v : Bool) :
    ordered (K := K) d l (!u) (!v) = sign l * ordered d l u v := by
  cases d <;> cases l <;> cases u <;> cases v <;> simp [ordered, sign]

/-- Native X edges at both ports preserve a Bell label up to its phase. -/
theorem native_sandwich (d l u v : Bool) :
    Kernel.mul (Kernel.mul Signature.disequality (ordered (K := K) d l))
      Signature.disequality u v = sign l * ordered d l u v := by
  rw [Kernel.disequality_sandwich, complement_both]

/-- Q8.32, an identity on all sixteen assignments, with no support hypothesis. -/
theorem y_square_closures (a b c d : Bool) :
    Y (K := K) a b * Y c d = X a d * X b c - X a c * X b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [Y, X, ordered, sign]

/-- The denominator-free form of Q8.34, restricted to exact weight two. -/
theorem equality_eo_closures (a b c d : Bool)
    (h : a.toNat + b.toNat + c.toNat + d.toNat = 2) :
    (2 : K) * (I a b * I c d) =
      X a c * X b d + X a d * X b c - X a b * X c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    (try norm_num [Bool.toNat] at h) <;>
    norm_num [I, X, ordered, sign]

/-- The final ordered three-matrix gadget of the Bell adjunction proof. -/
theorem y_x_i : Kernel.mul (Kernel.mul (Y (K := K)) X) I = Z := by
  funext u v
  cases u <;> cases v <;>
    simp [Kernel.mul_apply, Y, X, I, Z, ordered, sign]

end Paper2.Bell
