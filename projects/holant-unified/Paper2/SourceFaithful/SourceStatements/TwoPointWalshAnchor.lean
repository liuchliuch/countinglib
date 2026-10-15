import Paper2.HeightOne.Cyclic.ActualDressing
import Paper2.HeightOne.Cyclic.QuaternaryFourier
import Paper2.Tractable.KPresentation

/-! The root-of-unity part of source Lemma 3.15.  The binary used for phase
correction is a literal self-loop of the supplied four-port table. Repeated
attachments use that same actual binary, with every representative scale
retained. No rotation group or separately available phase card is assumed. -/
namespace Paper2.SourceFaithful.SourceStatements.TwoPointWalsh
open Paper2.Tractable Paper2.HeightOne.PhaseCards Paper2.HeightOne.GroupSplit
open Paper2.HeightOne.GroupSplit.MatrixGroup Paper2.HeightOne.Cyclic
open Paper2.HighHeightNormalization
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def endpoints (c r : AlgebraicComplex) : Signature AlgebraicComplex 4 :=
  fun x => c * (point (fun _ => false) x + r * point (fun _ => true) x)

lemma native_endpoints (q : Signature AlgebraicComplex 4) (c r : AlgebraicComplex)
    (hq : walshCoordinates q = endpoints c r) (x : Fin 4 → Bool) :
    q x = c * ((∏ i, walsh (x i) false) + r * ∏ i, walsh (x i) true) := by
  have h := congrFun (walsh_action_cancel q) x
  rw [hq] at h
  rw [← h]
  simp only [endpoints, action, mul_add, Finset.sum_add_distrib]
  simp [point, mul_assoc, mul_comm]

/-- The first two ordered occurrences become one actual native-X edge. -/
def loopBinary (q : Signature AlgebraicComplex 4) : AMat :=
  fun a b => Signature.contract Signature.disequality q ![a,b]

lemma loopBinary_realizable {F : SignatureFamily AlgebraicComplex}
    (q : Signature AlgebraicComplex 4) (hq : NetworkRealizable F q) :
    NetworkRealizable F (binaryTable (loopBinary q)) := by
  obtain ⟨N,hU,hX,hN⟩ := hq.ordered
  refine ⟨2,N.contract Signature.disequality,Equiv.refl _,hU.contract _,
    hX.contract,?_⟩
  rw [Network.denote_contract,hN]
  funext x
  change Signature.contract Signature.disequality q x =
    Signature.contract Signature.disequality q ![x 0,x 1]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- This is the transfer of the self-loop above, including its factor 4c. -/
lemma loopBinary_transfer (q : Signature AlgebraicComplex 4) (c r : AlgebraicComplex)
    (hq : walshCoordinates q = endpoints c r) :
    transfer (loopBinary q) = (4 * c) • phase r := by
  funext a b
  cases a <;> cases b <;>
    simp [transfer,loopBinary,Matrix.mul_apply,X,Signature.disequality,
      Signature.contract_disequality,native_endpoints q c r hq,
      Fin.prod_univ_succ,walsh,phase,balanced]
  all_goals ring

/-- Every attachment is an actual two-vertex splice; the empty list is q. -/
def phaseDress (q : Signature AlgebraicComplex 4) (m : ℕ) :
    Signature AlgebraicComplex 4 :=
  attachmentSequence (fun _ : Fin m => 0) (fun _ => loopBinary q) q

lemma phaseDress_realizable {F : SignatureFamily AlgebraicComplex}
    (q : Signature AlgebraicComplex 4) (hq : NetworkRealizable F q) (m : ℕ) :
    NetworkRealizable F (phaseDress q m) :=
  attachmentSequence_realizable _ _ q hq (fun _ => loopBinary_realizable q hq)

lemma phaseDress_walsh (q : Signature AlgebraicComplex 4) (c r : AlgebraicComplex)
    (hq : walshCoordinates q = endpoints c r) (m : ℕ) :
    walshCoordinates (phaseDress q m) = endpoints (c * (4 * c) ^ m) (r ^ (m+1)) := by
  rw [phaseDress,cyclic_attachmentSequence_walsh _ _ _ _
    (fun _ => loopBinary_transfer q c r hq),hq]
  funext x
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,endpoints]
  have hz : (fun _ : Fin 4 => false) ≠ (fun _ => true) := by
    intro h
    exact Bool.false_ne_true (congrFun h 0)
  by_cases h0 : x = (fun _ => false)
  · subst x
    simp [point,hz,mul_comm]
  by_cases h1 : x = (fun _ => true)
  · subst x
    simp [point,pow_succ,hz.symm]
    ring
  simp [point,h0,h1]

/-- K is exactly the manuscript's basis, with edge scale one. -/
lemma k_inverse_edge :
    Kernel.pullback Signature.disequality sourceKBasis.inverse = Signature.equality := by
  funext a b
  cases a <;> cases b <;>
    simp [sourceKBasis,Kernel.pullback,Kernel.mul_apply,Kernel.transpose,
      KInverse,Signature.disequality,Signature.equality,
      div_mul_div_comm,← pow_two,imaginaryUnit_sq,sqrtTwo_sq]
  all_goals ring

def equalityFour : Signature AlgebraicComplex 4 :=
  point (fun _ => false) + point (fun _ => true)

lemma k_walsh_diagonal :
    Kernel.mul sourceKBasis.matrix walsh =
      fun a b => if a = b then sqrtTwo * (if a then imaginaryUnit else 1) else 0 := by
  funext a b
  cases a <;> cases b <;>
    simp [sourceKBasis,KMatrix,walsh,Kernel.mul_apply]
  all_goals field_simp [sqrtTwo_ne_zero]
  all_goals ring_nf <;> norm_num [sqrtTwo_sq]

/-- The balanced two-point Walsh table gives the fixed K equality-four anchor. -/
lemma balanced_k_anchor (g : Signature AlgebraicComplex 4) (c : AlgebraicComplex)
    (hg : walshCoordinates g = endpoints c 1) :
    sourceKBasis.action g = fun x => (4 * c) * equalityFour x := by
  rw [← walsh_action_cancel g,hg]
  change Signature.coordinateAction (fun _ : Fin 4 => sourceKBasis.matrix)
    (action walsh (endpoints c 1)) = _
  rw [← action_eq_coordinateAction_four]
  rw [action_comp,k_walsh_diagonal]
  have hi : imaginaryUnit ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2*2 by decide,pow_mul,imaginaryUnit_sq]
    norm_num
  have hs : sqrtTwo ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2*2 by decide,pow_mul,sqrtTwo_sq]
    norm_num
  funext x
  simp only [action,endpoints,mul_add,Finset.sum_add_distrib,point,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Fin.prod_univ_succ,equalityFour,point,funext_iff,Fin.forall_fin_succ,
      h0,h1,h2,h3]
  all_goals (ring_nf; norm_num [hi,hs])

/-- Literal phase-order correction, including order one, uses no extra
available binary. The returned table is an actual graph over F. -/
theorem quaternary_root_anchor {F : SignatureFamily AlgebraicComplex}
    (q : Signature AlgebraicComplex 4) (hq : NetworkRealizable F q)
    (c r : AlgebraicComplex) (hc : c ≠ 0)
    (hform : walshCoordinates q = endpoints c r)
    (ell : ℕ) (hell : 0 < ell) (hr : r ^ ell = 1) :
    ∃ (g : Signature AlgebraicComplex 4) (lam : AlgebraicComplex),
      NetworkRealizable F g ∧ lam ≠ 0 ∧
      Kernel.pullback Signature.disequality sourceKBasis.inverse = Signature.equality ∧
      sourceKBasis.action g = fun x => lam * equalityFour x := by
  let g := phaseDress q (ell-1)
  let c' := c * (4*c) ^ (ell-1)
  have hc' : c' ≠ 0 := mul_ne_zero hc (pow_ne_zero _ (mul_ne_zero (by norm_num) hc))
  have hg : walshCoordinates g = endpoints c' 1 := by
    rw [phaseDress_walsh q c r hform,show ell-1+1=ell by omega,hr]
  exact ⟨g,4*c',phaseDress_realizable q hq _,mul_ne_zero (by norm_num) hc',
    k_inverse_edge,balanced_k_anchor g c' hg⟩

end
end Paper2.SourceFaithful.SourceStatements.TwoPointWalsh
