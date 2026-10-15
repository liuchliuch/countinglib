import Paper2.Paper1ProvedOddUnaryNRJordanPowers

/-! Actual positive ordinary Jordan chains and their unary pencil. Every
chain contains the original binary macro and original pin macro only; all
joining edges are literal equality and no zero-length identity is inserted. -/
namespace Paper2.Paper1Proved.OddUnary.JordanChain
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open OrdinaryNegativeCubicGadgets
open scoped BigOperators Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] {s : ℕ} {a : ℕ → ℕ}
variable {H : (i : Fin s) → Holant.Signature K (a i.val)}

abbrev binarySignature (B : Matrix Bool Bool K) : Holant.Signature K 2 := fun x => B (x 0) (x 1)

def series (N M : Macro H 2) : Macro H 2 :=
  ((N.tensor M).reindex C.seriesOrder).contract

theorem series_denote (N M : Macro H 2) (B D : Matrix Bool Bool K)
    (hN : N.network.denote=binarySignature B) (hM : M.network.denote=binarySignature D) :
    (series N M).network.denote=binarySignature (B*D) := by
  funext x
  rw [series,Macro.contract_denote,Macro.reindex_denote,Macro.tensor_denote,hN,hM]
  change B (x 0) false*D false (x 1)+B (x 0) true*D true (x 1) = _
  simp only [binarySignature,Matrix.mul_apply,Fintype.sum_bool]
  ring

def power (N : Macro H 2) : ℕ → Macro H 2
  | 0 => N
  | m+1 => series (power N m) N

theorem power_denote (N : Macro H 2) (B : Matrix Bool Bool K)
    (hN : N.network.denote=binarySignature B) (m : ℕ) :
    (power N m).network.denote=binarySignature (B^(m+1)) := by
  induction m with
  | zero => simpa only [power,Nat.zero_add,pow_one] using hN
  | succ m ih =>
    rw [power,series_denote _ _ _ _ ih hN,←pow_succ]

/-- Old [B0,B1,P0] becomes [B1,P0,B0]. -/
def capOrder : Equiv.Perm (Fin 3) where
  toFun := ![2,0,1]
  invFun := ![1,2,0]
  left_inv := by decide
  right_inv := by decide

def applyPin (N : Macro H 2) (P : Macro H 1) : Macro H 1 :=
  ((N.tensor P).reindex capOrder).contract

theorem applyPin_denote (N : Macro H 2) (P : Macro H 1) (B : Matrix Bool Bool K)
    (u : Bool → K) (hN : N.network.denote=binarySignature B)
    (hP : P.network.denote=fun x => u (x 0)) :
    (applyPin N P).network.denote=fun x => (B *ᵥ u) (x 0) := by
  funext x
  rw [applyPin,Macro.contract_denote,Macro.reindex_denote,Macro.tensor_denote,hN,hP]
  change B (x 0) false*u false+B (x 0) true*u true = _
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_bool]
  ring

variable {phi : K →+* AlgebraicComplex}
def binary (J : NRCanonical.JordanReceipt (H := H) phi) : Macro H 2 :=
  ⟨J.graph.network,J.graph.labels,J.graph.exact,J.graph.ordinary⟩

theorem binary_denote (J : NRCanonical.JordanReceipt (H := H) phi) :
    (binary J).network.denote=binarySignature (NRJordanPowers.receiptMatrix J) := by
  funext x
  change J.graph.network.denote x=J.graph.network.denote ![x 0,x 1]
  congr 1
  funext i
  fin_cases i <;> rfl

def query (J : NRCanonical.JordanReceipt (H := H) phi) (P : Macro H 1) (m : ℕ) : Macro H 1 :=
  applyPin (power (binary J) m) P

def left (J : NRCanonical.JordanReceipt (H := H) phi) : Holant.Signature K 1 :=
  fun x => J.eigenvalueK*(if x 0 then 0 else 1)
def right (J : NRCanonical.JordanReceipt (H := H) phi) : Holant.Signature K 1 :=
  fun x => J.defectK*(if x 0 then J.ratioK else 1)
def target (J : NRCanonical.JordanReceipt (H := H) phi) : K := -J.eigenvalueK/J.defectK
def targetScalar (J : NRCanonical.JordanReceipt (H := H) phi) : K := -J.eigenvalueK*J.ratioK

/-- The m+1 sample is the natural-node pencil, with its exact per-occurrence
scale. The seed pin is an actual original-family ordinary macro. -/
theorem query_denote (J : NRCanonical.JordanReceipt (H := H) phi)
    (injective : Function.Injective phi) (P : Macro H 1) (c : K)
    (hP : P.network.denote=fun x => NRJordanPowers.pin c (x 0)) (m : ℕ) :
    (query J P m).network.denote=fun x => J.eigenvalueK^m*c*
      (left J x+((m+1 : ℕ) : K)*right J x) := by
  rw [query,applyPin_denote _ _ _ _ (power_denote _ _ (binary_denote J) m) hP]
  rw [NRJordanPowers.receipt_positive_power_pin J injective m c]
  funext x
  cases h : x 0 <;> simp only [h,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    NRJordanPowers.pin,NRJordanPowers.repeated,left,right,ite_true,ite_false,
    Bool.false_eq_true,pow_succ]
  all_goals ring

theorem targetScalar_nonzero (J : NRCanonical.JordanReceipt (H := H) phi)
    (injective : Function.Injective phi) : targetScalar J≠0 :=
  mul_ne_zero (neg_ne_zero.mpr J.eigenvalueK_nonzero)
    (NRJordanPowers.repeated_true_nonzero _ (J.ratioK_square injective))

/-- At the fixed original-field target the pencil is the second literal pin. -/
theorem target_pin (J : NRCanonical.JordanReceipt (H := H) phi) :
    (fun x => left J x+target J*right J x)=
      fun x => targetScalar J*(if x 0 then 1 else 0) := by
  funext x
  cases h : x 0 <;> simp only [left,right,target,targetScalar,h,
    ite_true,ite_false,Bool.false_eq_true]
  all_goals field_simp [J.defectK_nonzero]
  all_goals ring

end
end Paper2.Paper1Proved.OddUnary.JordanChain
