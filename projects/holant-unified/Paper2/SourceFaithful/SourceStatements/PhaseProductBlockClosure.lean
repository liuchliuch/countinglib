import Paper2.HeightOne.PhaseCards.PhaseProduct

/-! Exact local block operations for source Lemma 5.11.  The class remains
the literal even-block tensor class; contraction closure is proved below. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductClosure
set_option backward.isDefEq.respectTransparency false
open Paper2.HeightOne.PhaseCards Paper2.Tractable
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 10000

variable {I J : Type} [Fintype I] [Fintype J]

theorem reindex_point (e : I ≃ J) (a : I → Bool) :
    Tensor.reindex e (point a) = point (fun j => a (e.symm j)) := by
  funext x
  have h : (fun i => x (e i)) = a ↔ x = fun j => a (e.symm j) := by
    constructor
    · intro h; funext j
      simpa using congrFun h (e.symm j)
    · intro h; funext i
      simpa using congrFun h (e i)
  simp only [Tensor.reindex_apply, point, h]

theorem reindex_twoPoint (e : I ≃ J) (a : I → Bool) (r : AlgebraicComplex) :
    Tensor.reindex e (twoPoint a r) = twoPoint (fun j => a (e.symm j)) r := by
  change Tensor.reindex e (point a + r • point (fun i => !(a i))) = _
  have h0 := reindex_point e a
  have h1 := reindex_point e (fun i => !(a i))
  funext x
  exact congrArg₂ (fun u v : AlgebraicComplex => u + r*v)
    (congrFun h0 x) (congrFun h1 x)

theorem twoPoint_complement (a : I → Bool) (r : AlgebraicComplex) (hr : r ≠ 0) :
    twoPoint a r = r • twoPoint (fun i => !(a i)) r⁻¹ := by
  funext x
  simp [twoPoint, point, hr, mul_add, Bool.not_not, add_comm]

omit [Fintype I] in
/-- Every nullary scalar is in the class, including zero. -/
theorem constant_empty (N : ℕ) [IsEmpty I] (c : AlgebraicComplex) :
    PhaseProduct N (fun _ : I → Bool => c) := by
  let D : TensorDecomposition AlgebraicComplex 0 :=
    { count := 0
      arity := fun i => Fin.elim0 i
      factor := fun i => Fin.elim0 i
      ports :=
        { toFun := fun p => Fin.elim0 p.1
          invFun := fun j => Fin.elim0 j
          left_inv := fun p => Fin.elim0 p.1
          right_inv := fun j => Fin.elim0 j }
      scale := 1 }
  let e : Fin 0 ≃ I := Equiv.equivOfIsEmpty _ _
  have h1 : PhaseProduct N (fun _ : I → Bool => (1 : AlgebraicComplex)) := by
    refine Or.inr ⟨0,D,e,fun i => Fin.elim0 i,?_⟩
    funext x
    simp [Tensor.reindex,D,TensorDecomposition.value]
  have hh := h1.scale c
  have he : c • (fun _ : I → Bool => (1 : AlgebraicComplex)) = (fun _ => c) := by
    funext x
    change c * 1 = c
    exact mul_one c
  rw [he] at hh
  exact hh

theorem twoPoint_member {N k : ℕ} (a : I → Bool) (r : AlgebraicComplex)
    (hcard : Fintype.card I = 2*(k+1)) (hr : PhaseRatio N (k+1) r) :
    PhaseProduct N (twoPoint a r) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have h : EvenPhaseBlock N (twoPoint (fun i => a (e i)) r) :=
    ⟨k,fun i => a (e i),r,hcard,hr,rfl⟩
  have hh := (PhaseProduct.of_block h).reindex e
  rw [reindex_twoPoint] at hh
  simpa only [Equiv.apply_symm_apply] using hh

omit [Fintype I] in
theorem contractKernel_four (E : Kernel AlgebraicComplex)
    (f : Tensor AlgebraicComplex (I ⊕ Bool)) (x : I → Bool) :
    contractKernel E f x =
      E false false*f (Sum.elim x (fun _ => false)) +
      E false true*f (Sum.elim x (fun b => b)) +
      E true false*f (Sum.elim x (fun b => !b)) +
      E true true*f (Sum.elim x (fun _ => true)) := by
  rw [contractKernel]
  calc
    _ = ∑ z : Bool × Bool, E z.1 z.2 *
        f (Sum.elim x (fun b => if b then z.2 else z.1)) := by
      apply Fintype.sum_equiv (Equiv.boolArrowEquivProd Bool)
      intro v
      congr 2
      funext q
      cases q with
      | inl i => rfl
      | inr b => cases b <;> rfl
    _ = _ := by simp [Fintype.sum_prod_type]; ring

/-- Two distinct blocks, with their selected port placed last and oriented
false. Both original block coefficients occur once in this literal tensor. -/
def cross (a : I → Bool) (b : J → Bool) (r t : AlgebraicComplex) :
    Tensor AlgebraicComplex ((I ⊕ J) ⊕ Bool) := fun x =>
  twoPoint (Sum.elim a (fun _ : Unit => false)) r
    (Sum.elim (fun i => x (.inl (.inl i))) (fun _ => x (.inr false))) *
  twoPoint (Sum.elim b (fun _ : Unit => false)) t
    (Sum.elim (fun j => x (.inl (.inr j))) (fun _ => x (.inr true)))

omit [Fintype I] [Fintype J] in
theorem sum_word_eq_iff (a y : I → Bool) (b z : J → Bool) :
    Sum.elim y z = Sum.elim a b ↔ y = a ∧ z = b := by
  constructor
  · intro h
    exact ⟨congrArg (fun q => fun i => q (.inl i)) h,
      congrArg (fun q => fun j => q (.inr j)) h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem twoPoint_last (a y : I → Bool) (r : AlgebraicComplex) (b : Bool) :
    twoPoint (Sum.elim a (fun _ : Unit => false)) r (Sum.elim y (fun _ => b)) =
      if b then r * point (fun i => !(a i)) y else point a y := by
  have hc : (fun q => !(Sum.elim a (fun _ : Unit => false) q)) =
      Sum.elim (fun i => !(a i)) (fun _ : Unit => true) := by
    funext q
    cases q <;> rfl
  have hn : (fun _ : Unit => false) ≠ (fun _ : Unit => true) := by
    intro h
    have hh := congrFun h ()
    exact Bool.false_ne_true hh
  cases b <;> simp [twoPoint,point,hc,sum_word_eq_iff,hn,Ne.symm hn]

theorem point_sum (a : I → Bool) (b : J → Bool) (x : I ⊕ J → Bool) :
    point (Sum.elim a b) x =
      point a (fun i => x (.inl i)) * point b (fun j => x (.inr j)) := by
  have he : x = Sum.elim a b ↔
      (fun i => x (.inl i)) = a ∧ (fun j => x (.inr j)) = b := by
    constructor
    · intro h
      exact ⟨congrArg (fun z => fun i => z (.inl i)) h,
        congrArg (fun z => fun j => z (.inr j)) h⟩
    · rintro ⟨ha,hb⟩
      funext i
      cases i with
      | inl i => exact congrFun ha i
      | inr j => exact congrFun hb j
  simp only [point,he]
  split_ifs <;> simp_all

omit [Fintype I] [Fintype J] in
theorem complement_sum (a : I → Bool) (b : J → Bool) :
    (fun i => !(Sum.elim a b i)) = Sum.elim (fun i => !(a i)) (fun j => !(b j)) := by
  funext i
  cases i <;> rfl

theorem cross_slice (a : I → Bool) (b : J → Bool) (r t : AlgebraicComplex)
    (x : I ⊕ J → Bool) (u v : Bool) :
    cross a b r t (Sum.elim x (fun q => if q then v else u)) =
      (if u then r*point (fun i => !(a i)) (fun i => x (.inl i))
        else point a (fun i => x (.inl i))) *
      (if v then t*point (fun j => !(b j)) (fun j => x (.inr j))
        else point b (fun j => x (.inr j))) := by
  change twoPoint (Sum.elim a (fun _ : Unit => false)) r
      (Sum.elim (fun i => x (.inl i)) (fun _ => u)) *
    twoPoint (Sum.elim b (fun _ : Unit => false)) t
      (Sum.elim (fun j => x (.inr j)) (fun _ => v)) = _
  rw [twoPoint_last,twoPoint_last]

theorem cross_plus (a : I → Bool) (b : J → Bool) (r t s : AlgebraicComplex) :
    contractKernel (plusKernel s) (cross a b r t) =
      twoPoint (Sum.elim a b) (-s*r*t) := by
  funext x
  have h00 := cross_slice a b r t x false false
  have h11 := cross_slice a b r t x true true
  simp only [ite_self, Bool.false_eq_true, ite_false, ite_true] at h00 h11
  unfold plusKernel
  rw [contractKernel_four]
  simp only [Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, zero_mul, add_zero, one_mul]
  rw [h00,h11]
  simp only [twoPoint,Pi.add_apply,Pi.smul_apply,smul_eq_mul,complement_sum,point_sum]
  ring

theorem cross_minus (a : I → Bool) (b : J → Bool) (r t s : AlgebraicComplex)
    (ht : t ≠ 0) :
    contractKernel (minusKernel s) (cross a b r t) =
      t • twoPoint (Sum.elim a (fun j => !(b j))) (-s*r*t⁻¹) := by
  funext x
  have h01 := cross_slice a b r t x false true
  have h10 := cross_slice a b r t x true false
  have hp01 : (fun q : Bool => if q then true else false) = (fun q => q) := by
    funext q; cases q <;> rfl
  have hp10 : (fun q : Bool => if q then false else true) = (fun q => !q) := by
    funext q; cases q <;> rfl
  rw [hp01] at h01
  rw [hp10] at h10
  simp only [Bool.false_eq_true, ite_false, ite_true] at h01 h10
  unfold minusKernel
  rw [contractKernel_four]
  simp only [Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,zero_mul,zero_add,add_zero,one_mul]
  rw [h01,h10]
  simp only [twoPoint,Pi.add_apply,Pi.smul_apply,smul_eq_mul,complement_sum,
    Bool.not_not,point_sum]
  field_simp [ht]

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductClosure

