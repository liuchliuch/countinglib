import Paper2.NetworkRealization
import Paper2.PrimeFactorization.PointMass
import Paper2.ExactInput.FiniteLanguage

/-! A literal native-X graph exposes any coordinate unary of an original
signature when both unit pins are actual members of the retained language.
Every other source port has its own opposite unit pin and oriented X edge;
the selected source port is the single ordered external boundary. -/
namespace Paper2.Paper1Proved.PinCoordinate
open Paper2.Tractable Paper2.ExactInput
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {n : ℕ}

def coordinateUnary (f : Signature AlgebraicComplex n) (i : Fin n) (x : Fin n → Bool) :
    Signature AlgebraicComplex 1 := fun z => f (Function.update x i (z 0))

abbrev Remaining (i : Fin n) := {j : Fin n // j ≠ i}

abbrev arity (i : Fin n) : Option (Remaining i) → ℕ
  | none => n
  | some _ => 1

def ports (i : Fin n) : (Σ v : Option (Remaining i), Fin (arity i v)) ≃
    (Fin 1 ⊕ (Remaining i × Bool)) where
  toFun p := match p with
    | ⟨none,j⟩ => if h : j=i then .inl 0 else .inr (⟨j,h⟩,false)
    | ⟨some k,_⟩ => .inr (k,true)
  invFun p := match p with
    | .inl _ => ⟨none,i⟩
    | .inr (k,false) => ⟨none,k.val⟩
    | .inr (k,true) => ⟨some k,(0 : Fin 1)⟩
  left_inv := by
    rintro ⟨v,j⟩
    cases v with
    | none => by_cases h : j=i <;> simp [h]
    | some k => have hj : j=(0 : Fin 1) := Fin.eq_zero j; subst j; rfl
  right_inv := by
    rintro (j | ⟨k,b⟩)
    · have hj : j=0 := Fin.eq_zero j
      subst j
      simp
    · cases b <;> simp [k.property]

def finite (f : Signature AlgebraicComplex n) (i : Fin n) (x : Fin n → Bool) :
    FiniteNetwork AlgebraicComplex (Option (Remaining i)) (Remaining i) 1 where
  arity := arity i
  ports := ports i
  vertex v := match v with
    | none => f
    | some k => TensorDecomposition.literalPin (!(x k.val))
  edge _ := Signature.disequality

def word (i : Fin n) (a : Fin 1 → Bool) (z : (Remaining i × Bool) → Bool) : Fin n → Bool :=
  fun j => if h : j=i then a 0 else z (⟨j,h⟩,false)

def assignment (i : Fin n) (x : Fin n → Bool) : (Remaining i × Bool) → Bool :=
  fun p => if p.2 then !(x p.1.val) else x p.1.val

theorem word_assignment (i : Fin n) (x : Fin n → Bool) (a : Fin 1 → Bool) :
    word i a (assignment i x)=Function.update x i (a 0) := by
  funext j
  by_cases h : j=i <;> simp [word,assignment,Function.update,h]

def factor (i : Fin n) (x : Fin n → Bool) (z : (Remaining i × Bool) → Bool) (k : Remaining i) :
    AlgebraicComplex :=
  TensorDecomposition.literalPin (!(x k.val)) (fun _ => z (k,true)) *
    Signature.disequality (z (k,false)) (z (k,true))

theorem factor_eq (i : Fin n) (x : Fin n → Bool) (z : (Remaining i × Bool) → Bool)
    (k : Remaining i) : factor i x z k =
      if z (k,false)=x k.val ∧ z (k,true)=!(x k.val) then 1 else 0 := by
  cases hx : x k.val <;> cases hf : z (k,false) <;> cases ht : z (k,true) <;>
    simp [factor,TensorDecomposition.literalPin,Signature.disequality,hx,hf,ht]

theorem factor_assignment (i : Fin n) (x : Fin n → Bool) (k : Remaining i) :
    factor i x (assignment i x) k=1 := by simp [factor_eq,assignment]

theorem product_zero (i : Fin n) (x : Fin n → Bool) (z : (Remaining i × Bool) → Bool)
    (hz : z≠assignment i x) : ∏ k, factor i x z k=0 := by
  classical
  have hb : ∃ k : Remaining i, ¬ (z (k,false)=x k.val ∧ z (k,true)=!(x k.val)) := by
    by_contra h
    push Not at h
    apply hz
    funext p
    rcases p with ⟨k,b⟩
    cases b
    · exact (h k).1
    · exact (h k).2
  obtain ⟨k,hk⟩ := hb
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [factor_eq,hk]

theorem finite_denote (f : Signature AlgebraicComplex n) (i : Fin n) (x : Fin n → Bool) :
    (finite f i x).denote=coordinateUnary f i x := by
  classical
  funext a
  have he : (finite f i x).denote a =
      ∑ z : (Remaining i × Bool) → Bool, f (word i a z)*(∏ k, factor i x z k) := by
    dsimp only [FiniteNetwork.denote,finite]
    apply Finset.sum_congr (by ext z; simp)
    intro z _
    rw [Fintype.prod_option]
    dsimp only
    have hw : (fun j : Fin n => Sum.elim a z ((ports i) ⟨none,j⟩))=word i a z := by
      funext j
      by_cases h : j=i <;> simp [ports,word,h]
    rw [hw]
    change (f (word i a z) * ∏ k, TensorDecomposition.literalPin (!(x k.val))
      (fun _ => z (k,true))) * (∏ k, Signature.disequality (z (k,false)) (z (k,true))) = _
    rw [mul_assoc,← Finset.prod_mul_distrib]
    rfl
  rw [he,Finset.sum_eq_single (assignment i x)]
  · simp [factor_assignment,word_assignment,coordinateUnary]
  · intro z _ hz
    rw [product_zero i x z hz,mul_zero]
  · simp

theorem coordinateUnary_realizable_family (F : SignatureFamily AlgebraicComplex)
    (f : Signature AlgebraicComplex n) (i : Fin n) (x : Fin n → Bool)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NetworkRealizable F (coordinateUnary f i x) := by
  let N := finite f i x
  refine ⟨1,N.toNetwork,Equiv.refl _,?_,?_,?_⟩
  · intro v
    change (⟨N.arity ((Fintype.equivFin (Option (Remaining i))).symm v),
      N.vertex ((Fintype.equivFin (Option (Remaining i))).symm v)⟩ : AnySignature AlgebraicComplex) ∈ F
    cases (Fintype.equivFin (Option (Remaining i))).symm v with
    | none => exact hf
    | some k => cases hx : x k.val <;> simpa [N,finite,arity,hx] using (by
        first | exact h1 | exact h0)
  · intro e
    rfl
  · rw [FiniteNetwork.denote_toNetwork]
    simpa only [Tensor.reindex_refl] using finite_denote f i x

theorem coordinateUnary_realizable (L : Language)
    (f : Signature AlgebraicComplex n) (i : Fin n) (x : Fin n → Bool)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    NetworkRealizable L.family (coordinateUnary f i x) :=
  coordinateUnary_realizable_family L.family f i x hf h0 h1

end
end Paper2.Paper1Proved.PinCoordinate
