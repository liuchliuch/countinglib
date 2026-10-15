import Paper2.Paper1ProvedOddUnaryNRSlices

/-! Exact scalar and port transport for the sheared tensor class. These
operations preserve the explicit ordered decomposition and do not require
any new generator or freely available signature. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant
noncomputable section
variable {K : Type*} [Field K]

/-- Every scalar multiple stays in the class, including the zero multiple. -/
theorem closed_scale {n : ℕ} (c : K) (f : Holant.Signature K n)
    (hf : Closed f) : Closed (fun x => c*f x) := by
  classical
  by_cases zero : c=0
  · left
    funext x
    simp [zero]
  rcases hf with rfl|⟨D,hD,rfl⟩
  · left
    funext x
    simp
  · let E : TensorDecomposition K n := { D with scale := Units.mk0 c zero * D.scale }
    refine Or.inr ⟨E,hD,?_⟩
    funext x
    simp only [TensorDecomposition.value,E,Units.val_mul,Units.val_mk0,mul_assoc]

/-- Nonzero normalization factors preserve and reflect the tensor criterion. -/
theorem closed_scale_iff {n : ℕ} (c : K) (hc : c≠0) (f : Holant.Signature K n) :
    Closed (fun x => c*f x) ↔ Closed f := by
  constructor
  · intro hf
    have h := closed_scale c⁻¹ (fun x => c*f x) hf
    simpa only [←mul_assoc,inv_mul_cancel₀ hc,one_mul] using h
  · exact closed_scale c f

/-- A port permutation is retained as an actual permutation of the ordered
block decomposition. -/
theorem closed_permute {n : ℕ} (f : Holant.Signature K n)
    (e : Fin n ≃ Fin n) (hf : Closed f) : Closed (fun x => f (fun j => x (e j))) := by
  rcases hf with rfl|⟨D,hD,rfl⟩
  · exact Or.inl rfl
  · let E : TensorDecomposition K n := { D with ports := D.ports.trans e }
    exact Or.inr ⟨E,hD,rfl⟩

theorem closed_permute_iff {n : ℕ} (f : Holant.Signature K n)
    (e : Fin n ≃ Fin n) : Closed (fun x => f (fun j => x (e j))) ↔ Closed f := by
  constructor
  · intro hf
    have h := closed_permute (fun x => f (fun j => x (e j))) e.symm hf
    simpa only [Equiv.symm_apply_apply] using h
  · exact closed_permute f e

@[simp] theorem slice_scale {n : ℕ} (c : K) (f : Holant.Signature K (n+1))
    (i : Fin (n+1)) (v : Bool) :
    slice (fun x => c*f x) i v=fun x => c*slice f i v x := rfl

end
end Paper2.Paper1Proved.OddUnary.NR

