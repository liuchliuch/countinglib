import Paper2.DegreeCSP.CodeSeven
import Paper2.DegreeCSP.MultiCoordinateContext
import Holant.Tractable.AffineOperations

/-! Every coordinate of an actual affine three-bit map is a constant or a
signed copy of one of the seven literal nonzero parity characters. This
decoder retains the original words on code inputs and assumes no XOR gate
or generated substitution implementation. -/
namespace Paper2.DegreeCSP.AffineThreeFaceDecoder
open MultiCoordinateContext (Expr eval word)
open Holant.Tractable.AffinePhase (Word origin basis xor)
open Holant.Tractable.TwoTranslate (IsAffineMap)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {n : ℕ}

def expression (b c₀ c₁ c₂ : Bool) : Expr 7 :=
  match Bool.xor c₀ b, Bool.xor c₁ b, Bool.xor c₂ b with
  | false,false,false => .inl b
  | true,false,false => .inr (0,b)
  | false,true,false => .inr (1,b)
  | false,false,true => .inr (2,b)
  | false,true,true => .inr (3,b)
  | true,false,true => .inr (4,b)
  | true,true,false => .inr (5,b)
  | true,true,true => .inr (6,b)

def decoder (p : Word 3 → Word n) : Fin n → Expr 7 := fun i =>
  expression (p (origin 3) i) (p (basis 0) i) (p (basis 1) i) (p (basis 2) i)

def bitWord (j : Fin 3) (b : Bool) : Word 3 := if b then basis j else origin 3

theorem word_split (z : Word 3) :
    z = xor (xor (bitWord 0 (z 0)) (bitWord 1 (z 1))) (bitWord 2 (z 2)) := by
  funext i
  fin_cases i <;> cases h₀ : z 0 <;> cases h₁ : z 1 <;> cases h₂ : z 2 <;>
    simp [bitWord,Holant.Tractable.AffinePhase.xor,basis,origin,h₀,h₁,h₂]

theorem affine_triple (p : Word 3 → Word n) (hp : IsAffineMap p)
    (x y z : Word 3) : p (xor (xor x y) z) = xor (xor (p x) (p y)) (p z) := by
  rw [hp,hp]
  funext i
  simp only [Holant.Tractable.AffinePhase.xor]
  cases p x i <;> cases p y i <;> cases p z i <;> cases p (origin 3) i <;> rfl

/-- The eight coefficient cases select exactly the displayed character,
with the original value at the origin as its Boolean sign. -/
theorem expression_value (b c₀ c₁ c₂ : Bool) (z : Word 3) :
    eval (expression b c₀ c₁ c₂) (GeneratedCodeSeven.code z) =
      Bool.xor (Bool.xor (if z 0 then c₀ else b) (if z 1 then c₁ else b))
        (if z 2 then c₂ else b) := by
  cases b <;> cases c₀ <;> cases c₁ <;> cases c₂ <;>
    cases h₀ : z 0 <;> cases h₁ : z 1 <;> cases h₂ : z 2 <;>
      simp [expression,eval,GeneratedCodeSeven.code,h₀,h₁,h₂]

/-- Literal word equality on the canonical code, at every original port. -/
theorem decoder_correct (p : Word 3 → Word n) (hp : IsAffineMap p) (z : Word 3) :
    word (decoder p) (GeneratedCodeSeven.code z) = p z := by
  have he := affine_triple p hp (bitWord 0 (z 0)) (bitWord 1 (z 1)) (bitWord 2 (z 2))
  rw [←word_split] at he
  funext i
  change eval (expression _ _ _ _) (GeneratedCodeSeven.code z) = p z i
  rw [expression_value,he]
  simp only [Holant.Tractable.AffinePhase.xor]
  cases z 0 <;> cases z 1 <;> cases z 2 <;> simp [bitWord]

theorem exists_decoder (p : Word 3 → Word n) (hp : IsAffineMap p) :
    ∃ E : Fin n → Expr 7, ∀ z, word E (GeneratedCodeSeven.code z) = p z :=
  ⟨decoder p,decoder_correct p hp⟩

theorem decoder_constant (p : Word 3 → Word n) (i : Fin n) (b : Bool)
    (h : ∀ z, p z i = b) : decoder p i = Sum.inl b := by
  simp only [decoder,h]
  cases b <;> rfl

/-- Actual retained coordinates are literal unflipped ports in the decoder. -/
theorem decoder_literal (p : Word 3 → Word n) (i : Fin n) (j : Fin 3)
    (h : ∀ z, p z i = z j) :
    decoder p i = Sum.inr (j.castLE (by decide : 3 ≤ 7),false) := by
  fin_cases j <;> simp [decoder,expression,h,origin,basis]

theorem decoder_signed_literal (p : Word 3 → Word n) (i : Fin n)
    (j : Fin 3) (b : Bool) (h : ∀ z, p z i = Bool.xor (z j) b) :
    decoder p i = Sum.inr (j.castLE (by decide : 3 ≤ 7),b) := by
  fin_cases j <;> cases b <;> simp [decoder,expression,h,origin,basis]

/-- Restrict the first r coordinates of a three-bit word. -/
def trim {r : ℕ} (hr : r ≤ 3) (z : Word 3) : Word r :=
  fun j => z (j.castLE hr)

/-- Literal false padding of a face with at most three free coordinates. -/
def pad {r : ℕ} (_hr : r ≤ 3) (z : Word r) : Word 3 :=
  fun j => if h : j.val < r then z ⟨j.val,h⟩ else false

theorem trim_pad {r : ℕ} (hr : r ≤ 3) (z : Word r) : trim hr (pad hr z) = z := by
  funext j
  simp [trim,pad,j.isLt]

theorem affine_trim {r : ℕ} (hr : r ≤ 3) (p : Word r → Word n)
    (hp : IsAffineMap p) : IsAffineMap (fun z : Word 3 => p (trim hr z)) :=
  fun x y => hp (trim hr x) (trim hr y)

/-- Actual affine faces of rank zero, one, two, or three all admit a literal
signed seven-port decoder after padding their input word with false bits. -/
theorem exists_decoder_of_rank_le_three {r : ℕ} (hr : r ≤ 3)
    (p : Word r → Word n) (hp : IsAffineMap p) :
    ∃ E : Fin n → Expr 7,
      ∀ z, word E (GeneratedCodeSeven.code (pad hr z)) = p z := by
  refine ⟨decoder (fun z => p (trim hr z)),?_⟩
  intro z
  rw [decoder_correct _ (affine_trim hr p hp),trim_pad]

end
end Paper2.DegreeCSP.AffineThreeFaceDecoder
