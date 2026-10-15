import Paper2.DegreeCSP.GeneratedCompose
import Paper2.DegreeCSP.GeneratedPullback
import Paper2.PrimeFactorization.PointMass

/-! Literal pins and coordinate restrictions are actual degree-generated
presentations. Repetition supplies a pin with degree k; restriction multiplies
by that pin and moves the retained variable to the hidden assignment sum. -/
namespace Paper2.DegreeCSP
open Tractable TensorDecomposition
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem generated_literalPin {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hk : 0 < k) (b : Bool)
    (hb : (⟨1,literalPin b⟩ : AnySignature AlgebraicComplex) ∈ F) :
    Generated F k (literalPin b) := by
  have h := generated_power F (literalPin b) hb (dvd_refl k)
  convert h using 1
  funext x
  by_cases hx : x 0=b
  · simp [literalPin,hx]
  · simp [literalPin,hx,Nat.ne_of_gt hk]

theorem generated_pin_last {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    {f : Signature AlgebraicComplex (n+1)} (hf : Generated F k f) (b : Bool)
    (hpin : Generated F k (literalPin b)) :
    Generated F k (fun x=>f (Fin.snoc x b)) := by
  have hp : Generated F k (fun x : Fin (n+1)→Bool=>
      literalPin b (fun _=>x (Fin.last n))) :=
    generated_pullback hpin (fun _ : Fin 1=>Fin.last n)
  have h := generated_sum_last (generated_hadamard hf hp)
  convert h using 1
  funext x
  cases b <;> simp [literalPin,Fintype.sum_bool]

/-- Moving i to the last variable and then restricting it keeps every other
coordinate in its original increasing order. -/
theorem insertLast_snoc {n : ℕ} (i : Fin (n+1)) (b : Bool) (x : Fin n→Bool) :
    (fun j=>Fin.snoc (α:=fun _=>Bool) x b
      (Fin.insertNth (α:=fun _=>Fin (n+1)) i (Fin.last n) (fun t=>t.castSucc) j)) =
      Fin.insertNth (α:=fun _=>Bool) i b x := by
  funext j
  induction j using Fin.succAboveCases i
  · simp
  · simp

theorem generated_pin_coordinate {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    {f : Signature AlgebraicComplex (n+1)} (hf : Generated F k f) (b : Bool)
    (hpin : Generated F k (literalPin b)) (i : Fin (n+1)) :
    Generated F k (fun x=>f (Fin.insertNth (α:=fun _=>Bool) i b x)) := by
  let r : Fin (n+1)→Fin (n+1) :=
    Fin.insertNth (α:=fun _=>Fin (n+1)) i (Fin.last n) (fun t=>t.castSucc)
  have hg := generated_pullback hf r
  have h := generated_pin_last hg b hpin
  convert h using 1
  funext x
  congr 1
  exact (insertLast_snoc i b x).symm

end
end Paper2.DegreeCSP
