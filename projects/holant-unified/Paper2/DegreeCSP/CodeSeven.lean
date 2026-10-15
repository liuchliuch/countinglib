import Paper2.Tractable.Affine
import Mathlib.Data.Fin.VecNotation

/-! The canonical seven nonconstant Boolean characters of a three-bit word,
ordered x,y,z,y xor z,x xor z,x xor y,x xor y xor z. -/
namespace Paper2.DegreeCSP.GeneratedCodeSeven
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

def code (x : Fin 3→Bool) : Fin 7→Bool :=
  ![x 0,x 1,x 2,Bool.xor (x 1) (x 2),Bool.xor (x 0) (x 2),
    Bool.xor (x 0) (x 1),Bool.xor (Bool.xor (x 0) (x 1)) (x 2)]

def decode (y : Fin 7→Bool) : Fin 3→Bool := ![y 0,y 1,y 2]

def Valid (y : Fin 7→Bool) : Prop :=
  y 3=Bool.xor (y 1) (y 2) ∧ y 4=Bool.xor (y 0) (y 2) ∧
    y 5=Bool.xor (y 0) (y 1) ∧ y 6=Bool.xor (y 5) (y 2)

instance (y : Fin 7→Bool) : Decidable (Valid y) := by
  unfold Valid
  infer_instance

def indicator (y : Fin 7→Bool) : AlgebraicComplex := if Valid y then 1 else 0

@[simp] theorem decode_code (x : Fin 3→Bool) : decode (code x)=x := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem valid_code (x : Fin 3→Bool) : Valid (code x) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem valid_iff_code (y : Fin 7→Bool) : Valid y ↔ y=code ![y 0,y 1,y 2] := by
  constructor
  · rintro ⟨h3,h4,h5,h6⟩
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact h3
    · exact h4
    · exact h5
    · change y 6=Bool.xor (Bool.xor (y 0) (y 1)) (y 2)
      rw [h6,h5]
  · intro h
    rw [h]
    exact valid_code _

@[simp] theorem indicator_code (x : Fin 3→Bool) : indicator (code x)=1 := by
  simp only [indicator,valid_code,ite_true]

end
end Paper2.DegreeCSP.GeneratedCodeSeven
