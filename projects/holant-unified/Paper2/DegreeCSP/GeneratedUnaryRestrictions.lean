import Paper2.DegreeCSP.GeneratedPins
import Paper2.DegreeCSP.GeneratedCoordinateRows

/-! Fixing an actual boundary prefix retains the exact unary table. The
all-zero prefix needs only the zero pin, and a boundary swap exposes any axis. -/
namespace Paper2.DegreeCSP
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem generated_unary_last_of_prefixPins {F : SignatureFamily AlgebraicComplex}
    {k n : ℕ} {f : Signature AlgebraicComplex (n+1)} (hf : Generated F k f)
    (a : Fin n→Bool) (hpin : ∀ i,Generated F k (literalPin (a i))) :
    Generated F k (fun z : Fin 1→Bool=>f (Fin.snoc a (z 0))) := by
  induction n with
  | zero =>
    convert hf using 1
    funext z
    congr 1
    funext i
    have hi : i=0 := Fin.eq_zero i
    subst i
    change Fin.snoc (α:=fun _=>Bool) a (z 0) (Fin.last 0)=z 0
    exact congrFun (Fin.snoc_zero a (z 0)) (Fin.last 0)
  | succ n ih =>
    let g : Signature AlgebraicComplex (n+1) := fun x=>f (Fin.cons (a 0) x)
    have hg : Generated F k g := by
      simpa only [Fin.insertNth_zero'] using generated_pin_coordinate hf (a 0) (hpin 0) 0
    have h := ih hg (fun j=>a j.succ) (fun j=>hpin j.succ)
    convert h using 1
    funext z
    change f (Fin.snoc a (z 0))=f (Fin.cons (a 0) (Fin.snoc (fun j=>a j.succ) (z 0)))
    rw [Fin.cons_snoc_eq_snoc_cons]
    congr 1
    congr 1
    funext i
    refine Fin.cases ?_ (fun j=>?_) i <;> simp

theorem generated_unary_last {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    {f : Signature AlgebraicComplex (n+1)} (hf : Generated F k f)
    (hpin0 : Generated F k (literalPin false)) (hpin1 : Generated F k (literalPin true))
    (a : Fin n→Bool) : Generated F k (fun z : Fin 1→Bool=>f (Fin.snoc a (z 0))) := by
  apply generated_unary_last_of_prefixPins hf a
  intro i
  cases ha : a i
  · exact hpin0
  · exact hpin1

theorem generated_unary_zero_last {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    {f : Signature AlgebraicComplex (n+1)} (hf : Generated F k f)
    (hpin0 : Generated F k (literalPin false)) :
    Generated F k (fun z : Fin 1→Bool=>f (Fin.snoc (fun _=>false) (z 0))) :=
  generated_unary_last_of_prefixPins hf (fun _=>false) (fun _=>hpin0)

theorem generated_unary_axis {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    {f : Signature AlgebraicComplex (n+1)} (hf : Generated F k f)
    (hpin0 : Generated F k (literalPin false)) (i : Fin (n+1)) :
    Generated F k (fun z : Fin 1→Bool=>f (Function.update (fun _=>false) i (z 0))) := by
  let e := Equiv.swap i (Fin.last n)
  let g : Signature AlgebraicComplex (n+1) := fun x=>f (fun j=>x (e j))
  have hg : Generated F k g := generated_reindex hf e
  have h := generated_unary_zero_last hg hpin0
  convert h using 1
  funext z
  congr 1
  exact (OriginalBO.swap_snoc_update i (fun _=>false) (z 0)).symm

end
end Paper2.DegreeCSP
