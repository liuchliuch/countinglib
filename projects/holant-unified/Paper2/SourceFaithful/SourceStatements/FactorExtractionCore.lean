import Paper2.SourceFaithful.SourceStatements.TwoPointWalshFactorAccess
import Paper2.PrimeFactorization
import Paper2.SourceFaithful.SourceStatements.PublicReduction
import Paper2.BellReduction.NetworkTensor

/-! Arbitrary two-factor extraction with literal ordered tensors and executed
strict public reductions. The factors need not be prime or positive-arity;
unrelated zero and nullary dictionary entries are retained. -/
namespace Paper2.SourceFaithful.SourceStatements.FactorExtraction
noncomputable section
open Paper2.Tractable Paper2.ExactInput Paper2.Paper1Proved
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ}

/-- Extract both specified factors, retaining the original tensor label. -/
theorem pair_access (L : Language) (a : Signature AlgebraicComplex m)
    (b : Signature AlgebraicComplex n) (hn : Signature.tensor a b ≠ 0)
    (hh : (⟨m+n,Signature.tensor a b⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (ht : ¬ CommonOneSided L.family) :
    ∃ M : Language,
      M.family = insert (⟨n,b⟩ : AnySignature AlgebraicComplex)
        (insert (⟨m,a⟩ : AnySignature AlgebraicComplex) L.family) ∧
      FixedFieldOutput.Reduces .nativeX M L ∧
      FixedFieldOutput.Reduces .nativeX L M := by
  let A := TensorDecomposition.singleton a
  let B := TensorDecomposition.singleton b
  let D := A.append B
  have hD : D.value = Signature.tensor a b := by
    simp [D,A,B,TensorDecomposition.value_append]
  have hleft : (⟨D.arity (A.appendIndexLeft B (0 : Fin 1)),
      D.factor (A.appendIndexLeft B (0 : Fin 1))⟩ : AnySignature AlgebraicComplex) = ⟨m,a⟩ :=
    TensorDecomposition.append_factor_left A B (0 : Fin 1)
  have hright : (⟨D.arity (A.appendIndexRight B (0 : Fin 1)),
      D.factor (A.appendIndexRight B (0 : Fin 1))⟩ : AnySignature AlgebraicComplex) = ⟨n,b⟩ :=
    TensorDecomposition.append_factor_right A B (0 : Fin 1)
  obtain ⟨P,hP,hPL,hLP⟩ := TwoPointWalshFactorAccess.factor_access L D
    (A.appendIndexLeft B (0 : Fin 1)) (by simpa only [hD] using hn)
    (by simpa only [hD] using hh) ht
  rw [hleft] at hP
  have hsub : L.family ⊆ P.family := by
    rw [hP]
    exact Set.subset_insert _ _
  have htP : ¬ CommonOneSided P.family :=
    fun hs => ht (hs.mono_family hsub)
  obtain ⟨M,hM,hMP,hPM⟩ := TwoPointWalshFactorAccess.factor_access P D
    (A.appendIndexRight B (0 : Fin 1)) (by simpa only [hD] using hn)
    (by simpa only [hD] using hsub hh) htP
  rw [hright,hP] at hM
  exact ⟨M,hM,hMP.trans hPL,hLP.trans hPM⟩

/-- A disconnected graph of two supplied vertices implements their full
ordered tensor, including either nullary factor. No tensor resource is free. -/
theorem tensor_realizable (F : SignatureFamily AlgebraicComplex)
    (a : Signature AlgebraicComplex m) (b : Signature AlgebraicComplex n)
    (ha : (⟨m,a⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hb : (⟨n,b⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NetworkRealizable F (Signature.tensor a b) := by
  let r : Bool → ℕ := fun q => if q then n else m
  let f : (q : Bool) → Signature AlgebraicComplex (r q) :=
    fun q => Bool.casesOn q a b
  let e : (Σ q : Bool, Fin (r q)) ≃ Fin (m+n) := {
    toFun := fun p => Bool.casesOn p.1 (Fin.castAdd n) (Fin.natAdd m) p.2
    invFun := fun i => Fin.addCases (m:=m) (n:=n) (fun j => ⟨false,j⟩) (fun j => ⟨true,j⟩) i
    left_inv := by rintro ⟨q,j⟩; cases q <;> simp
    right_inv := by
      intro i
      refine Fin.addCases (m:=m) (n:=n) (fun j => ?_) (fun j => ?_) i
      · dsimp only
        rw [Fin.addCases_left]
      · dsimp only
        rw [Fin.addCases_right] }
  have hr : NetworkRealizable F (Tensor.piTensor f) :=
    NetworkRealizable.piTensor r f (by intro q; cases q <;> assumption)
  have he : Tensor.reindex e (Tensor.piTensor f) = Signature.tensor a b := by
    funext x
    simp [Tensor.reindex,Tensor.piTensor,Signature.tensor_apply,f,r,e,mul_comm]
  exact he ▸ hr.reindex e

/-- Literal source Theorem 2.14 outside its common-side exception. Both
finite dictionaries are specified exactly: Lambda+h and Lambda+a+b. -/
theorem source_2_14_equivalence (L M : Language)
    (F : SignatureFamily AlgebraicComplex)
    (a : Signature AlgebraicComplex m) (b : Signature AlgebraicComplex n)
    (hL : L.family = insert (⟨m+n,Signature.tensor a b⟩ : AnySignature AlgebraicComplex) F)
    (hM : M.family = insert (⟨m,a⟩ : AnySignature AlgebraicComplex)
      (insert (⟨n,b⟩ : AnySignature AlgebraicComplex) F))
    (hn : Signature.tensor a b ≠ 0) (ht : ¬ CommonOneSided L.family) :
    Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  have hh : (⟨m+n,Signature.tensor a b⟩ : AnySignature AlgebraicComplex) ∈ L.family := by
    rw [hL]
    exact Set.mem_insert _ _
  obtain ⟨P,hP,hPL,_⟩ := pair_access L a b hn hh ht
  have hMP : M.family ⊆ P.family := by
    rw [hM,hP]
    rintro z (rfl | rfl | hz)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (by rw [hL]; exact Or.inr hz))
  have ha : (⟨m,a⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
    rw [hM]; exact Or.inl rfl
  have hb : (⟨n,b⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
    rw [hM]; exact Or.inr (Or.inl rfl)
  obtain ⟨Q,hQ,hQM⟩ := directGadgetProvider.adjoin M (Signature.tensor a b)
    (NativeNetworkRealizesUpTo.of_realizable (tensor_realizable M.family a b ha hb))
  have hLQ : L.family ⊆ Q.family := by
    rw [hL,hQ]
    rintro z (rfl | hz)
    · exact Or.inl rfl
    · exact Or.inr (by rw [hM]; exact Or.inr (Or.inr hz))
  exact ⟨PublicReduction.of_fixed_field .nativeX M L ((restriction M P hMP).trans hPL),
    PublicReduction.of_fixed_field .nativeX L M ((restriction L Q hLQ).trans hQM)⟩

end
end Paper2.SourceFaithful.SourceStatements.FactorExtraction

