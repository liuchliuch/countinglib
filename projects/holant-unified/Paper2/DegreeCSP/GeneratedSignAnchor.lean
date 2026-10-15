import Paper2.DegreeCSP.BooleanMinimalFace
import Paper2.DegreeCSP.GeneratedRestrictions
import Paper2.DegreeCSP.GeneratedHadamardUnary
import Paper2.Tractable.Product

/-! A nonconstant sign with its actual constant and axis terms removed has a
fixed two-coordinate AND face. Actual pins therefore retain a scaled Hadamard
anchor. The all-zero sign is instead a literal product of its unary axes. -/
namespace Paper2.DegreeCSP.GeneratedSignAnchor
open scoped BigOperators
open Tractable TensorDecomposition AxisRatioSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem product_axes {n : ℕ} (phi : Fin n→AlgebraicComplex) :
    Product (fun x : Fin n→Bool=>∏i,if x i then phi i else 1) := by
  classical
  have h : ∀s:Finset (Fin n),Product (fun x : Fin n→Bool=>∏i∈s,if x i then phi i else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using product_constant n 1
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using
        (product_unary i (fun b=>if b then phi i else 1)).mul ih
  simpa using h Finset.univ

theorem product_of_zero_sign {n : ℕ} (f : Signature AlgebraicComplex n)
    (c : AlgebraicComplex) (phi : Fin n→AlgebraicComplex) (P : (Fin n→Bool)→Bool)
    (hzero : ∀x,P x=false)
    (hform : ∀x,f x=c*(∏i,if x i then phi i else 1)*(if P x then -1 else 1)) :
    Product f := by
  have he : f=(fun x=>c*(∏i,if x i then phi i else 1)) := by
    funext x
    rw [hform x,hzero x]
    simp
  rw [he]
  exact (product_axes phi).scale c

/-- Minimality is applied only to actual displayed sign values. Its two free
coordinates are retained by the proved partial boundary restriction compiler. -/
theorem generated_anchor {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (c : AlgebraicComplex) (P : (Fin n→Bool)→Bool)
    (hG : Generated F k (fun x=>c*(if P x then -1 else 1)))
    (hp0 : Generated F k (literalPin false)) (hp1 : Generated F k (literalPin true))
    (hzero : P zeroWord=false)
    (haxis : ∀i,P (Function.update zeroWord i true)=false)
    (hex : ∃x,P x=true) :
    Generated F k (GeneratedHadamardUnary.anchor c) := by
  classical
  let Q : (Fin n→Bool)→ZMod 2 := fun x=>bitValue (ZMod 2) (P x)
  have hz : Q (fun _=>false)=0 := by
    change bitValue (ZMod 2) (P zeroWord)=0
    rw [hzero]
    rfl
  have hs : ∀i,Q (Function.update (fun _=>false) i true)=0 := by
    intro i
    simp only [Q,show (fun _ : Fin n=>false)=zeroWord from rfl,haxis i,bitValue_false]
  have hx : ∃x,Q x=1 := by
    obtain ⟨x,hx⟩ := hex
    exact ⟨x,by simp [Q,hx]⟩
  obtain ⟨z,i,j,hij,hface⟩ := BooleanMinimalFace.exists_and_face Q hz hs hx
  let r : Fin n→Option (Fin 2) := fun q=>if q=i then some 0 else if q=j then some 1 else none
  have h := generated_restrict hG hp0 hp1 r z
  have hp (b d : Bool) : P (Function.update (Function.update z i b) j d)= (b&&d) := by
    have he := hface b d
    change bitValue (ZMod 2) (P (Function.update (Function.update z i b) j d))=_ at he
    cases hpv:P (Function.update (Function.update z i b) j d) <;>
      cases b <;> cases d <;> simp [hpv,bitValue] at he ⊢
  rcases h with ⟨R,hR,hdiv,hvalue⟩
  refine ⟨R,hR,hdiv,?_⟩
  rw [hvalue]
  funext x
  dsimp only [GeneratedHadamardUnary.anchor]
  apply congrArg (fun b : Bool=>c*(if b then -1 else 1))
  rw [←hp (x 0) (x 1)]
  congr 1
  funext q
  by_cases hqi:q=i
  · subst q; simp [r,Function.update,hij]
  by_cases hqj:q=j
  · subst q; simp [r,Function.update,hqi]
  · simp [r,Function.update,hqi,hqj]

end
end Paper2.DegreeCSP.GeneratedSignAnchor
