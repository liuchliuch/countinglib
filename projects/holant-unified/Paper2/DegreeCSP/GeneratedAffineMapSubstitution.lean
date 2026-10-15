import Paper2.DegreeCSP.GeneratedAffineSubstitution
import Holant.Tractable.AffineOperations

/-! The original affine-map predicate determines the finite XOR-list circuit
from the map's literal values at the origin and coordinate words. -/
namespace Paper2.DegreeCSP.GeneratedAffineSubstitution
open Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Paper2.TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem evaluate_origin {m : ℕ} (l : List (Fin m)) :
    evaluate l false (origin m)=false := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change Bool.xor false (evaluate l false (origin m))=false
    rw [ih]
    rfl

private theorem evaluate_xor {m : ℕ} (l : List (Fin m)) (x y : Word m) :
    evaluate l false (xor x y)=Bool.xor (evaluate l false x) (evaluate l false y) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change Bool.xor (Bool.xor (x i) (y i)) (evaluate l false (xor x y))=
      Bool.xor (Bool.xor (x i) (evaluate l false x))
        (Bool.xor (y i) (evaluate l false y))
    rw [ih]
    cases x i <;> cases y i <;> cases evaluate l false x <;>
      cases evaluate l false y <;> rfl

private theorem evaluate_offset {m : ℕ} (l : List (Fin m)) (b : Bool) (x : Word m) :
    evaluate l b x=Bool.xor (evaluate l false x) b := by
  induction l with
  | nil => cases b <;> rfl
  | cons i l ih =>
    change Bool.xor (x i) (evaluate l b x)=
      Bool.xor (Bool.xor (x i) (evaluate l false x)) b
    rw [ih]
    cases x i <;> cases evaluate l false x <;> cases b <;> rfl

private theorem evaluate_basis {m : ℕ} (l : List (Fin m)) (hl : l.Nodup) (j : Fin m) :
    evaluate l false (basis j)=decide (j∈l) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hn : i∉l := (List.nodup_cons.mp hl).1
    have htail := ih (List.nodup_cons.mp hl).2
    change Bool.xor (decide (i=j)) (evaluate l false (basis j))=decide (j∈i::l)
    rw [htail]
    by_cases h : j=i
    · subst j
      simp [hn]
    · simp [h,Ne.symm h]

def affineIndices {m n : ℕ} (p : Word m→Word n) (i : Fin n) : List (Fin m) :=
  (List.finRange m).filter (fun j=>Bool.xor (p (basis j) i) (p (origin m) i))

/-- Each original affine coordinate is exactly its finite basis XOR list,
with its actual value at the origin as offset. -/
theorem affine_coordinate {m n : ℕ} (p : Word m→Word n) (hp : IsAffineMap p)
    (x : Word m) (i : Fin n) :
    evaluate (affineIndices p i) (p (origin m) i) x=p x i := by
  classical
  let q : Word m→ZMod 2 := fun y=>bitValue (ZMod 2)
    (Bool.xor (p y i) (p (origin m) i))
  let r : Word m→ZMod 2 := fun y=>bitValue (ZMod 2)
    (evaluate (affineIndices p i) false y)
  have hq0 : q (origin m)=0 := by
    dsimp [q]
    cases p (origin m) i <;> decide
  have hq (y z : Word m) : q (xor y z)=q y+q z := by
    have H := congrFun (hp y z) i
    dsimp [q]
    rw [H]
    change bitValue (ZMod 2)
      (Bool.xor (Bool.xor (p y i) (Bool.xor (p z i) (p (origin m) i)))
        (p (origin m) i))=_
    cases p y i <;> cases p z i <;> cases p (origin m) i <;> decide
  have hr0 : r (origin m)=0 := by
    simp only [r,evaluate_origin,bitValue_false]
  have hr (y z : Word m) : r (xor y z)=r y+r z := by
    simp only [r,evaluate_xor,bitValue_xor_two]
  have hb (j : Fin m) : q (basis j)=r (basis j) := by
    have hn : (affineIndices p i).Nodup :=
      (List.nodup_finRange m).filter _
    rw [show r (basis j)=bitValue (ZMod 2) (decide (j∈affineIndices p i)) from
      congrArg (bitValue (ZMod 2)) (evaluate_basis _ hn j)]
    simp only [affineIndices,List.mem_filter,List.mem_finRange,true_and]
    dsimp [q]
    cases p (basis j) i <;> cases p (origin m) i <;> decide
  have hqr := congrFun (additive_word_eq q r hq0 hr0 hq hr hb) x
  dsimp [q,r] at hqr
  rw [evaluate_offset]
  generalize he : evaluate (affineIndices p i) false x=e at *
  cases hpx : p x i <;> cases hpo : p (origin m) i <;> cases e <;>
    simp_all [bitValue]

/-- An original affine map is implemented by the proved actual XOR circuit.
The nonzero scale records all parity gates used by its finite coordinate lists. -/
theorem generated_substitution_of_isAffineMap
    {F : SignatureFamily AlgebraicComplex} {k m n : ℕ}
    (a : AlgebraicComplex) (ha : a≠0)
    (hanchor : Generated F k (GeneratedHadamardUnary.anchor a))
    (hpin0 : Generated F k (literalPin false)) (hpin1 : Generated F k (literalPin true))
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (p : Word m→Word n) (hp : IsAffineMap p) :
    ∃ c : AlgebraicComplex,c≠0 ∧ Generated F k (fun x=>c*f (p x)) := by
  obtain ⟨c,hc,hg⟩ := generated_substitution a ha hanchor hpin0 hpin1 f hf
    (affineIndices p) (p (origin m))
  refine ⟨c,hc,?_⟩
  convert hg using 1
  funext x
  congr 2
  funext i
  exact (affine_coordinate p hp x i).symm

end
end Paper2.DegreeCSP.GeneratedAffineSubstitution
