import Paper2.HeightOne.Dihedral.SixPortFactorization
import Paper2.HeightOne.PhaseCards.OrientedCards

/-! Analytic bit-index changes for the six-port reconstruction. Product
expressions, affine matching supports and each literal oriented contraction
are transported by explicit identities; these changes are not asserted to be
network gadgets. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Cyclic Tractable EndpointSelfLoop PhaseCards
open scoped BigOperators
local instance {ι : Type} : DecidableEq ι := Classical.decEq ι

lemma xorWord_twice {ι : Type} (a x : ι → Bool) : xorWord a (xorWord a x) = x := by
  funext i
  simp only [xorWord]
  cases a i <;> cases x i <;> rfl

lemma support_xorShift {K : Type*} [Field K] {ι : Type} [Fintype ι]
    (a : ι → Bool) (f : Tensor K ι) :
    support (xorShift a f) = (support f).image (xorWord a) := by
  classical
  ext x
  rw [mem_support,Finset.mem_image]
  constructor
  · intro hx
    exact ⟨xorWord a x,(mem_support _ _).mpr hx,xorWord_twice a x⟩
  · rintro ⟨y,hy,rfl⟩
    change f (xorWord a (xorWord a y)) ≠ 0
    rw [xorWord_twice]
    exact (mem_support _ _).mp hy

lemma reindex_xorShift {K : Type*} {ι κ : Type} (e : ι ≃ κ)
    (a : ι → Bool) (f : Tensor K ι) :
    Tensor.reindex e (xorShift a f) =
      xorShift (fun j => a (e.symm j)) (Tensor.reindex e f) := by
  funext y
  change f (fun i => a i ^^ y (e i)) = f (fun i => a (e.symm (e i)) ^^ y (e i))
  simp only [Equiv.symm_apply_apply]

lemma cosetCode_xorShift {n : ℕ} (P : Pairing n) (a b : Fin n → Bool) :
    (cosetCode P b).image (xorWord a) = cosetCode P (xorWord a b) := by
  classical
  rw [cosetCode,Finset.image_image]
  unfold cosetCode
  congr 1
  funext x i
  simp only [Function.comp_apply,xorWord]
  cases a i <;> cases b i <;> cases x i <;> rfl

lemma mem_cosetCode {n : ℕ} (P : Pairing n) (a x : Fin n → Bool) :
    x ∈ cosetCode P a ↔ ∀ j,
      (x (P.ports (j,false)) ^^ x (P.ports (j,true))) =
        (a (P.ports (j,false)) ^^ a (P.ports (j,true))) := by
  classical
  constructor
  · rintro hx j
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    have he := (mem_equalityCode P y).mp hy j
    simp only [xorWord,← he]
    cases a (P.ports (j,false)) <;> cases a (P.ports (j,true)) <;>
      cases y (P.ports (j,false)) <;> rfl
  · intro hx
    refine Finset.mem_image.mpr ⟨xorWord a x,?_,xorWord_twice a x⟩
    rw [mem_equalityCode]
    intro j
    have he := hx j
    simp only [xorWord]
    cases ha : a (P.ports (j,false)) <;> cases hb : a (P.ports (j,true)) <;>
      cases hx : x (P.ports (j,false)) <;> cases hy : x (P.ports (j,true)) <;>
      simp_all

lemma parity_pairing {n : ℕ} (P : Pairing n) (x : Fin n → Bool) :
    parity x = (∑ j : Fin P.count,
      ((if x (P.ports (j,false)) then 1 else 0) +
        (if x (P.ports (j,true)) then 1 else 0))) % 2 := by
  unfold parity weight
  rw [← P.ports.sum_comp (fun i => if x i then 1 else 0),Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,add_comm]

lemma cosetCode_parity {n : ℕ} (P : Pairing n) (a x y : Fin n → Bool)
    (hx : x ∈ cosetCode P a) (hy : y ∈ cosetCode P a) : parity x = parity y := by
  have H (b c : Bool) : ((if b then 1 else 0) + (if c then 1 else 0)) % 2 =
      (if b ^^ c then 1 else 0) := by cases b <;> cases c <;> decide
  rw [parity_pairing P x,parity_pairing P y]
  conv_lhs => rw [Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [H,H,(mem_cosetCode P a x).mp hx j,(mem_cosetCode P a y).mp hy j]

lemma CosetMatchingSupport.hasParity {K : Type*} [Field K] {ι : Type} [Fintype ι]
    {f : Tensor K ι} (h : CosetMatchingSupport f) : HasParity f := by
  obtain ⟨P,a,h⟩ := h
  intro x y hx hy
  let X : Fin (Fintype.card ι) → Bool := fun j => x ((Fintype.equivFin ι).symm j)
  let Y : Fin (Fintype.card ι) → Bool := fun j => y ((Fintype.equivFin ι).symm j)
  have hX : X ∈ cosetCode P a := by
    rw [← h,mem_support]
    simpa only [Tensor.reindex_apply,X,Equiv.symm_apply_apply] using hx
  have hY : Y ∈ cosetCode P a := by
    rw [← h,mem_support]
    simpa only [Tensor.reindex_apply,Y,Equiv.symm_apply_apply] using hy
  simpa only [X,Y,parity,weight_reindex] using cosetCode_parity P a X Y hX hY

theorem CosetMatchingSupport.xorShift {K : Type*} [Field K] {ι : Type} [Fintype ι]
    {f : Tensor K ι} (h : CosetMatchingSupport f) (a : ι → Bool) :
    CosetMatchingSupport (xorShift a f) := by
  obtain ⟨P,b,h⟩ := h
  let A : Fin (Fintype.card ι) → Bool := fun j => a ((Fintype.equivFin ι).symm j)
  have he : Tensor.reindex (Fintype.equivFin ι) (Dihedral.xorShift a f) =
      Dihedral.xorShift A (Tensor.reindex (Fintype.equivFin ι) f) := by
    funext y
    change f (fun i => a i ^^ y ((Fintype.equivFin ι) i)) =
      f (fun i => A ((Fintype.equivFin ι) i) ^^ y ((Fintype.equivFin ι) i))
    congr 1
    funext i
    simp [A]
  refine ⟨P,xorWord A b,?_⟩
  rw [he,support_xorShift,h,cosetCode_xorShift]

lemma CosetMatchingSupport.complement {K : Type*} [Field K] {ι : Type} [Fintype ι]
    {f : Tensor K ι} (h : CosetMatchingSupport f) (x : ι → Bool) (hx : f x ≠ 0) :
    f (fun i => !(x i)) ≠ 0 := by
  classical
  obtain ⟨P,a,h⟩ := h
  let X : Fin (Fintype.card ι) → Bool := fun j => x ((Fintype.equivFin ι).symm j)
  have hm : X ∈ cosetCode P a := by
    rw [← h,mem_support]
    simpa only [Tensor.reindex_apply,X,Equiv.symm_apply_apply] using hx
  obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hm
  have hcomp : (fun i => !(y i)) ∈ equalityCode P := by
    rw [mem_equalityCode] at hy ⊢
    exact fun i => congrArg Bool.not (hy i)
  have hXX : (fun j => !(X j)) ∈ cosetCode P a := by
    refine Finset.mem_image.mpr ⟨fun i => !(y i),hcomp,?_⟩
    rw [← he]
    funext i
    simp only [xorWord]
    cases a i <;> cases y i <;> rfl
  rw [← h,mem_support] at hXX
  simpa only [Tensor.reindex_apply,X,Equiv.symm_apply_apply] using hXX

def shiftedProductFactor {n : ℕ} (a : Fin n → Bool) : ProductFactor n → ProductFactor n
  | .unary j u hu => .unary j (fun b => u (a j ^^ b)) (by
      intro h
      apply hu
      funext b
      have hh := congrFun h (a j ^^ b)
      cases ha : a j <;> cases b <;> simpa [ha] using hh)
  | .equality j k => if a j = a k then .equality j k else .disequality j k
  | .disequality j k => if a j = a k then .disequality j k else .equality j k

lemma shiftedProductFactor_eval {n : ℕ} (a : Fin n → Bool) (p : ProductFactor n) :
    (shiftedProductFactor a p).eval = xorShift a p.eval := by
  funext x
  cases p with
  | unary j u hu => rfl
  | equality j k =>
    cases ha : a j <;> cases hb : a k <;> cases hx : x j <;> cases hy : x k <;>
      simp [shiftedProductFactor,ProductFactor.eval,xorShift,xorWord,ha,hb,hx,hy,
        Signature.equality,Signature.disequality]
  | disequality j k =>
    cases ha : a j <;> cases hb : a k <;> cases hx : x j <;> cases hy : x k <;>
      simp [shiftedProductFactor,ProductFactor.eval,xorShift,xorWord,ha,hb,hx,hy,
        Signature.equality,Signature.disequality]

theorem product_xorShift {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Product f) (a : Fin n → Bool) : Product (xorShift a f) := by
  rcases hf with rfl | ⟨c,hc,ps,rfl⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨c,hc,ps.map (shiftedProductFactor a),?_⟩
    funext x
    simp only [productFormula,xorShift,List.map_map,Function.comp_def,shiftedProductFactor_eval]

lemma extendBits_xor {ι : Type} [Fintype ι] (a : ι → Bool)
    (i j : ι) (hij : i ≠ j) (y : Remaining i j → Bool) (u v : Bool) :
    xorWord a (extendBits i j hij y u v) =
      extendBits i j hij (xorWord (restrict i j a) y) (a i ^^ u) (a j ^^ v) := by
  classical
  funext k
  by_cases hki : k = i
  · subst k; simp [xorWord,extendBits,splitPorts]
  by_cases hkj : k = j
  · subst k; simp [xorWord,extendBits,splitPorts,hij,Ne.symm hij]
  · simp [xorWord,extendBits,splitPorts,restrict,hki,hkj]

/-- A plus card after shifting the base word is precisely the shifted
oriented xor card of the original tensor, at the same phase. -/
lemma plusContraction_xorShift {ι : Type} [Fintype ι]
    (f : Tensor AlgebraicComplex ι) (a : ι → Bool)
    (i j : ι) (hij : i ≠ j) (s : AlgebraicComplex) :
    plusContraction i j hij s (xorShift a f) =
      xorShift (restrict i j a) (card (xorKernel (a i) (a j) s) i j hij f) := by
  funext y
  rw [plusContraction_apply]
  simp only [xorShift]
  rw [extendBits_xor,extendBits_xor,card_xor_apply]
  simp only [Bool.xor_false,Bool.xor_true]

lemma card_xorShift {ι : Type} [Fintype ι]
    (f : Tensor AlgebraicComplex ι) (a : ι → Bool)
    (i j : ι) (hij : i ≠ j) (u v : Bool) (s : AlgebraicComplex) :
    card (xorKernel u v s) i j hij (xorShift a f) =
      xorShift (restrict i j a) (card (xorKernel (a i ^^ u) (a j ^^ v) s) i j hij f) := by
  funext y
  rw [card_xor_apply]
  simp only [xorShift]
  rw [extendBits_xor,extendBits_xor,card_xor_apply]
  have H (b c : Bool) : (b ^^ (!c)) = !(b ^^ c) := by cases b <;> cases c <;> rfl
  rw [H,H]

end
end Paper2.HeightOne.Dihedral

