import Paper2.ExactInput.FixedRootCodec.SquarefreeReduction
import Paper2.ExactInput.FixedRootCodec.SturmCountEuclidean

/-! The actual bounded Euclidean program generates a negative remainder
chain. Its first terminal pair has a nonzero constant first component for
coprime polynomial and derivative. The full fixed-size program repeats
this terminal constant, so it needs no variable stopping-time program. -/
namespace Paper2.ExactInput.FixedRootCodec.VariablePolynomial
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines Polynomial
open FixedGadgetSubstitution.Compiler
noncomputable section

def terminationIndex {n : ℕ} (v : Fin n → ℚ) : ℕ :=
  Nat.find (⟨n,gcdStage_terminal (v,derivative v)⟩ :
    ∃ k, (gcdStage (v,derivative v) k).2=0)

theorem terminationIndex_spec {n : ℕ} (v : Fin n → ℚ) :
    (gcdStage (v,derivative v) (terminationIndex v)).2=0 := by
  unfold terminationIndex
  exact Nat.find_spec (p := fun k => (gcdStage (v,derivative v) k).2=0)
    ⟨n,gcdStage_terminal (v,derivative v)⟩

theorem terminationIndex_le {n : ℕ} (v : Fin n → ℚ) : terminationIndex v ≤ n :=
  Nat.find_min' _ (gcdStage_terminal (v,derivative v))

theorem before_termination_ne {n : ℕ} (v : Fin n → ℚ) (k : ℕ)
    (hk : k < terminationIndex v) : (gcdStage (v,derivative v) k).2 ≠ 0 :=
  Nat.find_min _ hk

theorem terminationIndex_pos {n : ℕ} (v : Fin n → ℚ) (hd : derivative v ≠ 0) :
    0 < terminationIndex v := by
  by_contra h
  have hz : terminationIndex v=0 := by omega
  have ht := terminationIndex_spec v
  rw [hz] at ht
  exact hd ht

def generatedTerm {n : ℕ} (v : Fin n → ℚ) (k : ℕ) : Fin n → ℚ :=
  (gcdStage (v,derivative v) k).1

def generatedTermComputes (n k : ℕ) :
    Computes (vectorEncoding n) (vectorEncoding n) (fun v => generatedTerm v k) :=
  congrComputes (((initialComputes n).andThen (gcdStageComputes n k)).andThen
    (Wiring.firstComputes _ _)) (fun _ => rfl)

def generatedTerms {n : ℕ} (v : Fin n → ℚ) : List (Fin n → ℚ) :=
  (List.range (n+2)).map (generatedTerm v)

def generatedTermsComputes (n : ℕ) :
    Computes (vectorEncoding n) (framedListEncoding (vectorEncoding n))
      (generatedTerms (n := n)) :=
  fixedListComputes _ _ generatedTerm (generatedTermComputes n) (List.range (n+2))

@[simp] theorem generatedTerm_zero {n : ℕ} (v : Fin n → ℚ) : generatedTerm v 0=v := rfl

theorem generatedTerm_succ {n : ℕ} (v : Fin n → ℚ) (k : ℕ)
    (hk : k < terminationIndex v) :
    generatedTerm v (k+1)=(gcdStage (v,derivative v) k).2 := by
  simp only [generatedTerm,gcdStage,gcdStep,before_termination_ne v k hk,ite_false]

theorem generatedTerm_one {n : ℕ} (v : Fin n → ℚ) (hd : derivative v ≠ 0) :
    generatedTerm v 1=derivative v := by
  simpa only [gcdStage] using generatedTerm_succ v 0 (terminationIndex_pos v hd)

theorem generatedTerm_prefix_ne {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (k : ℕ) (hk : k ≤ terminationIndex v) : generatedTerm v k ≠ 0 := by
  cases k with
  | zero => exact hv
  | succ k =>
    have hk' : k < terminationIndex v := by omega
    rw [generatedTerm_succ v k hk']
    exact before_termination_ne v k hk'

theorem gcdStage_stable {n : ℕ} (p : Pair n) (k t : ℕ) (hk : (gcdStage p k).2=0) :
    gcdStage p (k+t)=gcdStage p k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ,gcdStage,ih]
    simp [gcdStep,hk]

theorem generatedTerm_after {n : ℕ} (v : Fin n → ℚ) (k : ℕ)
    (hk : terminationIndex v ≤ k) : generatedTerm v k=generatedTerm v (terminationIndex v) := by
  have h := gcdStage_stable (v,derivative v) (terminationIndex v)
    (k-terminationIndex v) (terminationIndex_spec v)
  rw [Nat.add_sub_of_le hk] at h
  exact congrArg Prod.fst h

theorem generatedTerm_recurrence {n : ℕ} (v : Fin n → ℚ) (i : ℕ)
    (hi : i+1 < terminationIndex v) :
    polynomial (generatedTerm v i) =
      (polynomial (generatedTerm v i) / polynomial (generatedTerm v (i+1))) *
        polynomial (generatedTerm v (i+1)) - polynomial (generatedTerm v (i+2)) := by
  have hi0 : i < terminationIndex v := by omega
  have hs := generatedTerm_succ v (i+1) hi
  have hnext : polynomial (generatedTerm v (i+2)) =
      -(polynomial (generatedTerm v i) % polynomial (generatedTerm v (i+1))) := by
    rw [show i+2=(i+1)+1 by omega,hs]
    simp only [gcdStage,gcdStep,before_termination_ne v i hi0,ite_false]
    rw [negate_polynomial,remainder_polynomial,generatedTerm_succ v i hi0]
    rfl
  rw [hnext]
  have hm := EuclideanDomain.mod_add_div' (polynomial (generatedTerm v i))
    (polynomial (generatedTerm v (i+1)))
  linear_combination -hm

theorem generatedTerminal_isUnit {n : ℕ} (v : Fin n → ℚ)
    (hcop : ∀ a : ℚ[X], a ∣ polynomial v → a ∣ (polynomial v).derivative → IsUnit a) :
    IsUnit (polynomial (generatedTerm v (terminationIndex v))) := by
  have hc := gcdStage_common_divisor (v,derivative v) (terminationIndex v)
    (polynomial (generatedTerm v (terminationIndex v)))
  have hd : polynomial (generatedTerm v (terminationIndex v)) ∣ polynomial v ∧
      polynomial (generatedTerm v (terminationIndex v)) ∣ polynomial (derivative v) := by
    apply hc.mp
    exact ⟨dvd_rfl,by rw [terminationIndex_spec,polynomial_zero]; exact dvd_zero _⟩
  exact hcop _ hd.1 (by simpa only [derivative_polynomial] using hd.2)

def generatedTerminal {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  (polynomial (generatedTerm v (terminationIndex v))).coeff 0

theorem generatedTerminal_polynomial {n : ℕ} (v : Fin n → ℚ)
    (hcop : ∀ a : ℚ[X], a ∣ polynomial v → a ∣ (polynomial v).derivative → IsUnit a) :
    polynomial (generatedTerm v (terminationIndex v))=C (generatedTerminal v) :=
  eq_C_of_degree_eq_zero (isUnit_iff_degree_eq_zero.mp (generatedTerminal_isUnit v hcop))

theorem generatedTerminal_ne_zero {n : ℕ} (v : Fin n → ℚ)
    (hcop : ∀ a : ℚ[X], a ∣ polynomial v → a ∣ (polynomial v).derivative → IsUnit a) :
    generatedTerminal v ≠ 0 := by
  have ht := (generatedTerminal_isUnit v hcop).ne_zero
  rw [generatedTerminal_polynomial v hcop] at ht
  exact C_ne_zero.mp ht

def generatedNegativeChain {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : derivative v ≠ 0)
    (hcop : ∀ a : ℚ[X], a ∣ polynomial v → a ∣ (polynomial v).derivative → IsUnit a) :
    SturmCount.NegativeRemainderChain where
  tailLength := terminationIndex v-1
  polynomial := fun i => (polynomial (generatedTerm v i)).map (algebraMap ℚ ℝ)
  quotient := fun i => (polynomial (generatedTerm v i) /
    polynomial (generatedTerm v (i+1))).map (algebraMap ℚ ℝ)
  head_ne := by
    simpa only [generatedTerm_zero] using
      (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr
        ((polynomial_eq_zero_iff v).not.mpr hv)
  derivative := by
    rw [generatedTerm_one v hd,generatedTerm_zero,derivative_polynomial,derivative_map]
  terminal := generatedTerminal v
  terminal_ne := by exact_mod_cast generatedTerminal_ne_zero v hcop
  last := by
    have hm : terminationIndex v-1+1=terminationIndex v := by
      have hp := terminationIndex_pos v hd
      omega
    rw [hm,generatedTerminal_polynomial v hcop,Polynomial.map_C]
    rfl
  recurrence := by
    intro i hi
    have hi' : i+1 < terminationIndex v := by
      have hp := terminationIndex_pos v hd
      omega
    simpa only [Polynomial.map_sub,Polynomial.map_mul] using
      congrArg (Polynomial.map (algebraMap ℚ ℝ)) (generatedTerm_recurrence v i hi')

theorem generatedNegativeChain_head {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : derivative v ≠ 0)
    (hcop : ∀ a : ℚ[X], a ∣ polynomial v → a ∣ (polynomial v).derivative → IsUnit a) :
    (generatedNegativeChain v hv hd hcop).polynomial 0=(polynomial v).map (algebraMap ℚ ℝ) := rfl

theorem generatedNegativeChain_length_bound {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : derivative v ≠ 0)
    (hcop : ∀ a : ℚ[X], a ∣ polynomial v → a ∣ (polynomial v).derivative → IsUnit a) :
    (generatedNegativeChain v hv hd hcop).tailLength+1 ≤ n := by
  change terminationIndex v-1+1 ≤ n
  have hm := terminationIndex_le v
  have hp := terminationIndex_pos v hd
  omega

def generatedDoubledVariation {n : ℕ} (v : Fin n → ℚ) (x : ℝ) : ℤ :=
  (∑ i ∈ Finset.range (n+1),
    (1-SturmCount.integerSign (((polynomial (generatedTerm v i)).map (algebraMap ℚ ℝ)).eval x)*
      SturmCount.integerSign (((polynomial (generatedTerm v (i+1))).map (algebraMap ℚ ℝ)).eval x))) -
    if ((polynomial v).map (algebraMap ℚ ℝ)).eval x=0 then 1 else 0

theorem generatedDoubledVariation_eq {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : derivative v ≠ 0)
    (hcop : ∀ a : ℚ[X], a ∣ polynomial v → a ∣ (polynomial v).derivative → IsUnit a)
    (x : ℝ) :
    generatedDoubledVariation v x=(generatedNegativeChain v hv hd hcop).toChain.doubledVariation x := by
  have hp := terminationIndex_pos v hd
  have hm := terminationIndex_le v
  have hs : (∑ i ∈ Finset.range (terminationIndex v),
      (1-SturmCount.integerSign (((polynomial (generatedTerm v i)).map (algebraMap ℚ ℝ)).eval x)*
        SturmCount.integerSign (((polynomial (generatedTerm v (i+1))).map (algebraMap ℚ ℝ)).eval x))) =
      ∑ i ∈ Finset.range (n+1),
      (1-SturmCount.integerSign (((polynomial (generatedTerm v i)).map (algebraMap ℚ ℝ)).eval x)*
        SturmCount.integerSign (((polynomial (generatedTerm v (i+1))).map (algebraMap ℚ ℝ)).eval x)) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hnot
    have him : terminationIndex v ≤ i := by simpa using hnot
    rw [generatedTerm_after v i him,generatedTerm_after v (i+1) (by omega),
      generatedTerminal_polynomial v hcop,Polynomial.map_C,Polynomial.eval_C]
    have hn : (generatedTerminal v : ℝ) ≠ 0 := by exact_mod_cast generatedTerminal_ne_zero v hcop
    exact sub_eq_zero.mpr (SturmCount.integerSign_sq hn).symm
  unfold generatedDoubledVariation SturmCount.Chain.doubledVariation
  simp only [SturmCount.Chain.signs,SturmCount.NegativeRemainderChain.toChain,generatedNegativeChain]
  have he : terminationIndex v-1+1=terminationIndex v := by omega
  rw [he,← hs]
  rfl

theorem generatedDoubledVariation_constant {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hdegree : (polynomial v).natDegree=0) (x : ℝ) :
    generatedDoubledVariation v x=0 := by
  have hd : derivative v=0 := by
    apply (polynomial_eq_zero_iff _).mp
    rw [derivative_polynomial,derivative_of_natDegree_zero hdegree]
  have ht (i : ℕ) : generatedTerm v i=v := by
    have hs := gcdStage_stable (v,derivative v) 0 i hd
    simpa only [Nat.zero_add,gcdStage,generatedTerm] using congrArg Prod.fst hs
  have hc := eq_C_of_natDegree_eq_zero hdegree
  have hn : (polynomial v).coeff 0 ≠ 0 := by
    intro hz
    have hp : polynomial v ≠ 0 := (polynomial_eq_zero_iff v).not.mpr hv
    exact hp (by simpa only [hz,C_0] using hc)
  have hn' : ((polynomial v).coeff 0 : ℝ) ≠ 0 := by exact_mod_cast hn
  have he : ((polynomial v).map (algebraMap ℚ ℝ)).eval x = (polynomial v).coeff 0 := by
    calc
      _ = ((C ((polynomial v).coeff 0)).map (algebraMap ℚ ℝ)).eval x :=
        congrArg (fun p : ℚ[X] => (p.map (algebraMap ℚ ℝ)).eval x) hc
      _ = _ := by rw [Polynomial.map_C,Polynomial.eval_C]; rfl
  unfold generatedDoubledVariation
  simp only [ht,he,SturmCount.integerSign_sq hn',
    sub_self,Finset.sum_const_zero,hn',ite_false]

def squarefreeNegativeChain {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : (polynomial (squarefreeVector v)).natDegree ≠ 0) :
    SturmCount.NegativeRemainderChain :=
  generatedNegativeChain (squarefreeVector v) (squarefreeVector_ne_zero v hv)
    (by
      apply (polynomial_eq_zero_iff _).not.mp
      rw [derivative_polynomial]
      exact squarefreeVector_derivative_ne_zero v hd)
    (squarefreeVector_common_divisor_isUnit v hv)

theorem squarefreeGeneratedVariation_eq {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : (polynomial (squarefreeVector v)).natDegree ≠ 0) (x : ℝ) :
    generatedDoubledVariation (squarefreeVector v) x=
      (squarefreeNegativeChain v hv hd).toChain.doubledVariation x := by
  unfold squarefreeNegativeChain
  exact generatedDoubledVariation_eq _ _ _ _ x

theorem squarefreeNegativeChain_roots {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : (polynomial (squarefreeVector v)).natDegree ≠ 0) :
    (squarefreeNegativeChain v hv hd).toChain.roots =
      ((polynomial v).map (algebraMap ℚ ℝ)).roots.toFinset := by
  classical
  ext x
  rw [SturmCount.Chain.mem_roots_iff]
  change ((polynomial (squarefreeVector v)).map (algebraMap ℚ ℝ)).eval x = 0 ↔ _
  rw [eval_map,squarefreeVector_real_roots v hv]
  simp only [Multiset.mem_toFinset,Polynomial.mem_roots_map_of_injective
    (algebraMap ℚ ℝ).injective ((polynomial_eq_zero_iff v).not.mpr hv)]

theorem squarefreeNegativeChain_count_Ioc {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : (polynomial (squarefreeVector v)).natDegree ≠ 0)
    (a b : ℝ) (hab : a ≤ b) :
    (squarefreeNegativeChain v hv hd).toChain.doubledVariation a-
      (squarefreeNegativeChain v hv hd).toChain.doubledVariation b =
      2*((((polynomial v).map (algebraMap ℚ ℝ)).roots.toFinset.filter
        fun r => a < r ∧ r ≤ b).card : ℤ) := by
  simpa only [squarefreeNegativeChain_roots] using
    (squarefreeNegativeChain v hv hd).count_Ioc a b hab

theorem squarefreeGeneratedVariation_count_Ioc {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : (polynomial (squarefreeVector v)).natDegree ≠ 0)
    (a b : ℝ) (hab : a ≤ b) :
    generatedDoubledVariation (squarefreeVector v) a-
      generatedDoubledVariation (squarefreeVector v) b =
      2*((((polynomial v).map (algebraMap ℚ ℝ)).roots.toFinset.filter
        fun r => a < r ∧ r ≤ b).card : ℤ) := by
  rw [squarefreeGeneratedVariation_eq v hv hd a,squarefreeGeneratedVariation_eq v hv hd b]
  exact squarefreeNegativeChain_count_Ioc v hv hd a b hab

theorem squarefree_no_root_of_derivative_zero {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : derivative (squarefreeVector v)=0)
    {K : Type*} [Field K] [CharZero K] (φ : ℚ →+* K) (x : K) :
    (polynomial v).eval₂ φ x ≠ 0 := by
  have hdp : (polynomial (squarefreeVector v)).derivative=0 := by
    rw [← derivative_polynomial,hd,polynomial_zero]
  have hc := eq_C_of_derivative_eq_zero hdp
  have hn : (polynomial (squarefreeVector v)).coeff 0 ≠ 0 := by
    intro hz
    have hp : polynomial (squarefreeVector v) ≠ 0 :=
      (polynomial_eq_zero_iff _).not.mpr (squarefreeVector_ne_zero v hv)
    exact hp (by simpa only [hz,C_0] using hc)
  apply (squarefreeVector_eval₂_zero_iff v hv φ x).not.mp
  rw [hc,eval₂_C]
  exact fun hz => hn (φ.injective (by simpa only [map_zero] using hz))

theorem squarefree_original_real_roots_empty {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hd : derivative (squarefreeVector v)=0) :
    ((polynomial v).map (algebraMap ℚ ℝ)).roots.toFinset=∅ := by
  classical
  ext x
  simp only [Multiset.mem_toFinset,Polynomial.mem_roots_map_of_injective
    (algebraMap ℚ ℝ).injective ((polynomial_eq_zero_iff v).not.mpr hv),Finset.notMem_empty,iff_false]
  exact squarefree_no_root_of_derivative_zero v hv hd _ x

end
end Paper2.ExactInput.FixedRootCodec.VariablePolynomial
