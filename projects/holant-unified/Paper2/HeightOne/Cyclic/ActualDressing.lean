import Paper2.HighHeightNormalization.FiniteAttachments
import Paper2.HeightOne.Cyclic.ActualQuaternary

/-! Literal native-X binary attachments on the four original ordered ports.
The Walsh diagonal formula is an identity for the same actual graph, with its
nonzero representative scale retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhaseCards GroupSplit GroupSplit.MatrixGroup
open Paper2.HighHeightNormalization
open scoped BigOperators

def fourBitsEquiv : (Fin 4 → Bool) ≃ (Bool × Bool × Bool × Bool) where
  toFun x := (x 0, x 1, x 2, x 3)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

lemma sum_four_assignments (f : Signature AlgebraicComplex 4) :
    (∑ x : Fin 4 → Bool, f x) =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f ![a,b,c,d] := by
  rw [← fourBitsEquiv.symm.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

def localMatrix (a : Fin 4) (T : Kernel AlgebraicComplex) : Fin 4 → Kernel AlgebraicComplex :=
  fun j => if j = a then T else Signature.equality

lemma update_four (x : Fin 4 → Bool) (a : Fin 4) (t : Bool) :
    Function.update x a t = ![if 0 = a then t else x 0,
      if 1 = a then t else x 1, if 2 = a then t else x 2, if 3 = a then t else x 3] := by
  funext i
  fin_cases i <;> simp [Function.update]

lemma action_eq_coordinateAction_four (M : Kernel AlgebraicComplex)
    (f : Signature AlgebraicComplex 4) :
    action M f = Signature.coordinateAction (fun _ => M) f := by
  classical
  funext x
  unfold action Signature.coordinateAction
  exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)

lemma attachment_coordinateAction_four (a : Fin 4) (B : Kernel AlgebraicComplex)
    (f : Signature AlgebraicComplex 4) :
    attachment a B f = Signature.coordinateAction
      (localMatrix a (fun x y => B (!y) x)) f := by
  funext x
  have he : x = ![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
  rw [he]
  fin_cases a <;> cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3
  all_goals simp [attachment, Signature.coordinateAction, localMatrix,
    sum_four_assignments, Fintype.sum_bool, Fin.prod_univ_succ, Signature.equality,
    update_four, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals ring

lemma localMatrix_action_diagonal (a : Fin 4) (c s : AlgebraicComplex)
    (f : Signature AlgebraicComplex 4) :
    Signature.coordinateAction
      (localMatrix a (fun x y => if x = y then c * (if x then s else 1) else 0)) f =
        fun x => c * (if x a then s else 1) * f x := by
  funext x
  have he : x = ![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
  rw [he]
  fin_cases a <;> cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3
  all_goals simp [Signature.coordinateAction, localMatrix,
    sum_four_assignments, Fintype.sum_bool, Fin.prod_univ_succ, Signature.equality]

lemma cyclic_attachment_local_matrix {B : AMat} {c s : AlgebraicComplex}
    (hB : transfer B = c • phase s) :
    Kernel.mul walshInv (Kernel.mul (fun x y => B (!y) x) walsh) =
      fun x y => if x = y then c * (if x then s else 1) else 0 := by
  rw [matrix_of_transfer hB]
  funext x y
  cases x <;> cases y <;>
    simp [Kernel.mul, Matrix.mul_apply, phase, balanced, X, Signature.disequality,
      walsh, walshInv, Matrix.smul_apply, Fintype.sum_bool] <;> field_simp <;> ring

/-- The exact single-port Walsh multiplier for the actual binary orientation
used by `attachmentFiniteNetwork`. -/
theorem cyclic_attachment_walsh (a : Fin 4) (f : Signature AlgebraicComplex 4)
    {B : AMat} {c s : AlgebraicComplex} (hB : transfer B = c • phase s) :
    walshCoordinates (attachment a B f) =
      fun x => c * (if x a then s else 1) * walshCoordinates f x := by
  have hcancel : Signature.coordinateAction (fun _ : Fin 4 => walsh)
      (walshCoordinates f) = f := by
    rw [← action_eq_coordinateAction_four]
    exact walsh_action_cancel f
  conv_lhs => rw [attachment_coordinateAction_four, ← hcancel]
  rw [walshCoordinates_eq_coordinateAction]
  change Signature.coordinateAction (fun _ => walshInv)
    (Signature.coordinateAction (localMatrix a (fun x y => B (!y) x))
      (Signature.coordinateAction (fun _ => walsh) (walshCoordinates f))) = _
  rw [Signature.coordinateAction_comp, Signature.coordinateAction_comp]
  have hmat : (fun j : Fin 4 => Kernel.mul walshInv
      (Kernel.mul (localMatrix a (fun x y => B (!y) x) j) walsh)) =
      localMatrix a (fun x y => if x = y then c * (if x then s else 1) else 0) := by
    funext j
    by_cases hj : j = a
    · simp only [localMatrix, if_pos hj]
      exact cyclic_attachment_local_matrix hB
    · simp only [localMatrix, if_neg hj]
      rw [Kernel.equality_mul]
      exact walshInv_mul_walsh
  simp_rw [Kernel.mul_assoc]
  rw [hmat]
  exact localMatrix_action_diagonal a c s (walshCoordinates f)

/-- Every finite sequence of rotation representatives has the displayed
portwise character weights.  Repeated ports are permitted in this identity. -/
theorem cyclic_attachmentSequence_walsh {m : ℕ} (ports : Fin m → Fin 4)
    (B : Fin m → AMat) (c s : Fin m → AlgebraicComplex)
    (hB : ∀ j, transfer (B j) = c j • phase (s j))
    (f : Signature AlgebraicComplex 4) :
    walshCoordinates (attachmentSequence ports B f) =
      fun x => (∏ j, c j) * (∏ j, if x (ports j) then s j else 1) * walshCoordinates f x := by
  induction m with
  | zero => simp [attachmentSequence]
  | succ m ih =>
    rw [attachmentSequence, cyclic_attachment_walsh (ports 0) _ (hB 0),
      ih (fun j => ports j.succ) (fun j => B j.succ)
        (fun j => c j.succ) (fun j => s j.succ) (fun j => hB j.succ)]
    funext x
    simp only [Fin.prod_univ_succ]
    ring

/-- Dressing is one actual native-X graph over the original language.  Its
Walsh scalar is nonzero and is the product of the recorded binary scales. -/
theorem actual_four_port_dressing {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (C : RotationCards F N) (f : Signature AlgebraicComplex 4)
    (hf : NetworkRealizable F f) (r : Fin 4 → rootsOfUnity N AlgebraicComplex) :
    ∃ (h : Signature AlgebraicComplex 4) (c : AlgebraicComplex),
      NetworkRealizable F h ∧ c ≠ 0 ∧
      walshCoordinates h = fun x =>
        c * (∏ j, if x j then ((r j).val : AlgebraicComplex) else 1) * walshCoordinates f x := by
  let h := attachmentSequence (fun j : Fin 4 => j) (fun j => C.binary (r j)) f
  refine ⟨h, ∏ j, C.scale (r j), ?_, ?_, ?_⟩
  · exact attachmentSequence_realizable _ _ f hf (fun j => (C.actual (r j)).1)
  · exact Finset.prod_ne_zero_iff.mpr (fun j _ => C.scale_ne_zero (r j))
  · exact cyclic_attachmentSequence_walsh _ _ _ _ (fun j => C.transfer_eq (r j)) f

end
end Paper2.HeightOne.Cyclic
