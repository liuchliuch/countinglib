import Paper2.DegreeCSP.EqualityTemplateLayout
import Mathlib.Data.List.OfFn

/-! The complete literal row lists of the arithmetic equality templates.
Their order is the order emitted by the actual compiler. -/
namespace Paper2.DegreeCSP.EqualityTemplates
open Paper2.Tractable Paper2.ExactInput
open Holant.Complexity Holant.Complexity.RawClosedNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def positiveRow (m k : ℕ) (hk : 3 ≤ k) (label outer inner : ℕ)
    (v : Fin (m+(m-1)*2)) : RawVertex :=
  (label,List.ofFn (fun j : Fin k => serializedEndpoint outer inner
    ((positive m k hk).shape.ports ⟨v,j⟩)))

theorem positive_main_row {m k : ℕ} (hk : 3 ≤ k) (label outer inner : ℕ) (t : Fin m) :
    positiveRow m k hk label outer inner (vertexEquiv m (.inl t)) =
      (label,List.ofFn (fun j : Fin k => ComputationLayout.mainEndpoint k m outer inner t.val j.val)) := by
  unfold positiveRow
  congr 1
  apply congrArg List.ofFn
  funext j
  exact positive_main_endpoint hk outer inner t j

theorem positive_firstConnector_row {m k : ℕ} (hk : 3 ≤ k) (label outer inner : ℕ)
    (t : Fin (m-1)) :
    positiveRow m k hk label outer inner (vertexEquiv m (.inr (t,false))) =
      (label,List.ofFn (fun j : Fin k => ComputationLayout.firstConnectorEndpoint k outer inner t.val j.val)) := by
  unfold positiveRow
  congr 1
  apply congrArg List.ofFn
  funext j
  exact positive_firstConnector_endpoint hk outer inner t j

theorem positive_secondConnector_row {m k : ℕ} (hk : 3 ≤ k) (label outer inner : ℕ)
    (t : Fin (m-1)) :
    positiveRow m k hk label outer inner (vertexEquiv m (.inr (t,true))) =
      (label,List.ofFn (fun j : Fin k => ComputationLayout.secondConnectorEndpoint k inner t.val j.val)) := by
  unfold positiveRow
  congr 1
  apply congrArg List.ofFn
  funext j
  exact positive_secondConnector_endpoint hk outer inner t j

/-- Main rows first, followed by the ordered connector pair at each link. -/
theorem positive_rows (m k : ℕ) (hk : 3 ≤ k) (label outer inner : ℕ) :
    List.ofFn (positiveRow m k hk label outer inner) =
      (List.finRange m).map (fun t =>
        (label,List.ofFn (fun j : Fin k => ComputationLayout.mainEndpoint k m outer inner t.val j.val))) ++
      (List.finRange (m-1)).flatMap (fun t =>
        [ (label,List.ofFn (fun j : Fin k => ComputationLayout.firstConnectorEndpoint k outer inner t.val j.val)),
          (label,List.ofFn (fun j : Fin k => ComputationLayout.secondConnectorEndpoint k inner t.val j.val)) ]) := by
  rw [List.ofFn_add]
  apply congrArg₂ List.append
  · rw [← List.ofFn_eq_map]
    apply congrArg List.ofFn
    funext t
    have he : t.castLE (Nat.le_add_right m ((m-1)*2)) = vertexEquiv m (.inl t) := by
      apply Fin.ext
      rfl
    rw [he]
    exact positive_main_row hk label outer inner t
  · rw [List.ofFn_mul,List.flatMap_def,← List.ofFn_eq_map]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext t
    simp only [List.ofFn_succ,List.ofFn_zero]
    have h0 : (⟨t.val*2+0,by omega⟩ : Fin ((m-1)*2)).natAdd m =
        vertexEquiv m (.inr (t,false)) := by
      apply Fin.ext
      simp [vertexEquiv_connector_val]
      ring
    have h1 : (⟨t.val*2+1,by omega⟩ : Fin ((m-1)*2)).natAdd m =
        vertexEquiv m (.inr (t,true)) := by
      apply Fin.ext
      simp [vertexEquiv_connector_val]
      ring
    simp only [Fin.val_zero,Fin.val_succ,zero_add]
    rw [h0,h1,positive_firstConnector_row,positive_secondConnector_row]

def nullaryRow (k label outer inner : ℕ) (v : Fin 2) : RawVertex :=
  (label,List.ofFn (fun j : Fin k => serializedEndpoint outer inner ((nullary k).shape.ports ⟨v,j⟩)))

theorem nullary_rows (k label outer inner : ℕ) : List.ofFn (nullaryRow k label outer inner) =
    [ (label,List.ofFn (fun j : Fin k => (inner+j.val,false))),
      (label,List.ofFn (fun j : Fin k => (inner+j.val,true))) ] := by
  simp only [List.ofFn_succ,List.ofFn_zero]
  change [nullaryRow k label outer inner (0 : Fin 2),nullaryRow k label outer inner (1 : Fin 2)] = _
  have h0 : nullaryRow k label outer inner (0 : Fin 2) =
      (label,List.ofFn (fun j : Fin k => (inner+j.val,false))) := rfl
  have h1 : nullaryRow k label outer inner (1 : Fin 2) =
      (label,List.ofFn (fun j : Fin k => (inner+j.val,true))) := rfl
  rw [h0,h1]

end
end Paper2.DegreeCSP.EqualityTemplates
