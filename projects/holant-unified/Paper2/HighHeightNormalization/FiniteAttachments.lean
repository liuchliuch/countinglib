import Paper2.HighHeightNormalization.AttachmentNetwork
import Paper2.HighHeightNormalization.Attachments
import Paper2.RelativeEO.AlgebraicARS
import Paper2.Paper1Accepted.Terminals

/-! Exact finite original-language compilation of the ordered normalization
attachments. Only actual supplied or already realized binary factors are used.
This does not assume that a formal ARS factor has been adjoined. -/
namespace Paper2.HighHeightNormalization
open Tractable ExactInput
variable {K : Type} [CommSemiring K] {n : ℕ}

/-- A single supplied table has a one-vertex, edgeless implementation. -/
theorem supplied_realizable {F : SignatureFamily K} {f : Signature K n}
    (hf : (⟨n,f⟩ : AnySignature K) ∈ F) : NetworkRealizable F f := by
  let e : (Σ _ : Unit, Fin n) ≃ Fin n := {
    toFun := fun p => p.2
    invFun := fun i => ⟨(),i⟩
    left_inv := by rintro ⟨u,i⟩; cases u; rfl
    right_inv := fun _ => rfl }
  have h := NetworkRealizable.piTensor (F := F) (fun _ : Unit => n)
    (fun _ => f) (fun _ => hf)
  have he : Tensor.reindex e (Tensor.piTensor (fun _ : Unit => f)) = f := by
    funext x
    simp [Tensor.reindex,Tensor.piTensor,e]
  exact he ▸ h.reindex e

/-- Both vertices are substituted by their actual original-language graphs. -/
theorem attachment_realizable_inputs {F : SignatureFamily K} (a : Fin n)
    (B : Kernel K) (M : Signature K n)
    (hM : NetworkRealizable F M) (hB : NetworkRealizable F (binaryTable B)) :
    NetworkRealizable F (attachment a B M) := by
  have hr := NetworkRealizable.substitute (F := F) (attachmentFiniteNetwork a B M).toNetwork
    (fun _ => rfl) (fun v => ?_)
  · rw [FiniteNetwork.denote_toNetwork,attachmentFiniteNetwork_denote] at hr
    exact hr
  · change NetworkRealizable F
      ((attachmentFiniteNetwork a B M).vertex ((Fintype.equivFin Bool).symm v))
    cases (Fintype.equivFin Bool).symm v
    · exact hM
    · exact hB

/-- The order is the same recursive order used by `attachFamily`. -/
noncomputable def attachmentSequence : {m : ℕ} → (Fin m → Fin n) →
    (Fin m → Kernel K) → Signature K n → Signature K n
  | 0,_,_,M => M
  | m+1,ports,B,M => attachment (ports 0) (B 0)
      (attachmentSequence (fun j : Fin m => ports j.succ) (fun j => B j.succ) M)

/-- A finite attachment sequence is one actual gadget over the original inputs;
no central tensor or synthesized intermediate vertex is treated as free. -/
theorem attachmentSequence_realizable {F : SignatureFamily K} {m : ℕ}
    (ports : Fin m → Fin n) (B : Fin m → Kernel K) (M : Signature K n)
    (hM : NetworkRealizable F M) (hB : ∀ j, NetworkRealizable F (binaryTable (B j))) :
    NetworkRealizable F (attachmentSequence ports B M) := by
  induction m with
  | zero => exact hM
  | succ m ih =>
    exact attachment_realizable_inputs (ports 0) (B 0) _
      (ih (fun j => ports j.succ) (fun j => B j.succ) (fun j => hB j.succ)) (hB 0)

/-- Finite literal augmentation with genuine root-coded machine reductions in
both directions, through only the accepted Paper 1 direct-gadget convention. -/
theorem attachmentSequence_adjoin (DG : Paper1DirectGadgetAccepted)
    (R : Paper1RestrictionAccepted) (L : Language) {m : ℕ}
    (ports : Fin m → Fin n) (B : Fin m → Kernel AlgebraicComplex)
    (M : Signature AlgebraicComplex n) (hM : NetworkRealizable L.family M)
    (hB : ∀ j, NetworkRealizable L.family (binaryTable (B j))) :
    ∃ N : Language,
      N.family = insert (⟨n,attachmentSequence ports B M⟩ : AnySignature AlgebraicComplex)
        L.family ∧ Problem.Reduces .nativeX N L ∧ Problem.Reduces .nativeX L N :=
  DG.adjoin_equivalence R L _ (NativeNetworkRealizesUpTo.of_realizable
    (attachmentSequence_realizable ports B M hM hB))

/-- The ARS binary lives in the original exact algebraic field. -/
noncomputable def algebraicBinary (z : AlgebraicComplex) : Kernel AlgebraicComplex :=
  WeightedMatching.binary z (RelativeEO.conjugateAlgebraic z)

@[simp] theorem coe_algebraicBinary (z : AlgebraicComplex) (a b : Bool) :
    (algebraicBinary z a b : ℂ) = binary (z : ℂ) a b := by
  cases a <;> cases b <;> rfl

/-- No change of scalar field is hidden by the complex-valued normalization API. -/
theorem attachment_coe (a : Fin n) (B : Kernel AlgebraicComplex)
    (M : Signature AlgebraicComplex n) :
    (fun x => (attachment (K := AlgebraicComplex) a B M x : ℂ)) =
      attach a (fun u v => (B u v : ℂ)) (fun x => (M x : ℂ)) := by
  funext x
  simp [attachment,attach,Fintype.sum_bool,Signature.disequality]
  congr 4 <;> funext i <;> by_cases hi : i = a <;> simp [Function.update,hi]

/-- The already proved `attachFamily` coefficient identities apply to the actual
finite algebraic graph, not just to an unrelated formal complex tensor. -/
theorem attachmentSequence_coe {m : ℕ} (ports : Fin m → Fin n)
    (z : Fin m → AlgebraicComplex) (M : Signature AlgebraicComplex n) :
    (fun x => (attachmentSequence (K := AlgebraicComplex) ports (fun j => algebraicBinary (z j)) M x : ℂ)) =
      attachFamily ports (fun j => (z j : ℂ)) (fun x => (M x : ℂ)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (fun x => (attachment (K := AlgebraicComplex) (ports 0) (algebraicBinary (z 0)) _ x : ℂ)) = _
    rw [attachment_coe]
    have hb : (fun u v => (algebraicBinary (z 0) u v : ℂ)) = binary (z 0 : ℂ) := by
      funext u v
      exact coe_algebraicBinary _ _ _
    rw [hb,ih]
    rfl

end Paper2.HighHeightNormalization
