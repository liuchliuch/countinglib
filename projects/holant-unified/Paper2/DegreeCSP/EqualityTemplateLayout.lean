import Paper2.DegreeCSP.EqualityTemplates
import Paper2.DegreeCSP.ComputationLayout

/-! The serialized arithmetic endpoints of the deterministic templates.
Boundary ends use the incoming true side of the original occurrence edge;
internal ends retain their explicit native-X orientations. -/
namespace Paper2.DegreeCSP.EqualityTemplates
open Paper2.Tractable Paper2.ExactInput
open Holant.Complexity Holant.Complexity.RawClosedNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def serializedEndpoint {d e : ℕ} (outer inner : ℕ) : Fin d ⊕ (Fin e × Bool) → RawEndpoint
  | .inl q => (outer+q.val,true)
  | .inr (q,b) => (inner+q.val,b)

theorem positive_main_endpoint {m k : ℕ} (hk : 3 ≤ k) (outer inner : ℕ)
    (t : Fin m) (j : Fin k) :
    serializedEndpoint outer inner
      ((positive m k hk).shape.ports ⟨vertexEquiv m (.inl t),j⟩) =
      ComputationLayout.mainEndpoint k m outer inner t.val j.val := by
  change serializedEndpoint outer inner (positivePorts m k hk _) = _
  rw [positivePorts_named]
  by_cases h0 : j.val=0 ∧ 0<t.val
  · simp [namedPorts,Equiv.coe_fn_mk,serializedEndpoint,ComputationLayout.mainEndpoint,h0,
      edgeEquiv,finProdFinEquiv,prev,one] <;> ring
  · by_cases h1 : j.val=1 ∧ t.val<m-1
    · have h1' : j.val=1 ∧ t.val+1<m := by omega
      simp [namedPorts,Equiv.coe_fn_mk,serializedEndpoint,ComputationLayout.mainEndpoint,h0,h1,h1',
        edgeEquiv,finProdFinEquiv,current,zero] <;> ring
    · have h1' : ¬(j.val=1 ∧ t.val+1<m) := by omega
      simp [namedPorts,Equiv.coe_fn_mk,serializedEndpoint,ComputationLayout.mainEndpoint,h0,h1,h1',
        boundaryEquiv,finProdFinEquiv] <;> ring

theorem positive_firstConnector_endpoint {m k : ℕ} (hk : 3 ≤ k) (outer inner : ℕ)
    (t : Fin (m-1)) (j : Fin k) :
    serializedEndpoint outer inner
      ((positive m k hk).shape.ports ⟨vertexEquiv m (.inr (t,false)),j⟩) =
      ComputationLayout.firstConnectorEndpoint k outer inner t.val j.val := by
  change serializedEndpoint outer inner (positivePorts m k hk _) = _
  rw [positivePorts_named]
  by_cases h0 : j.val=0
  · simp [namedPorts,Equiv.coe_fn_mk,serializedEndpoint,ComputationLayout.firstConnectorEndpoint,h0,
      boundaryEquiv,finProdFinEquiv,base,one] <;> ring
  · by_cases h1 : j.val=1
    · simp [namedPorts,Equiv.coe_fn_mk,serializedEndpoint,ComputationLayout.firstConnectorEndpoint,h0,h1,
        boundaryEquiv,finProdFinEquiv,next,zero] <;> ring
    · simp [namedPorts,Equiv.coe_fn_mk,serializedEndpoint,ComputationLayout.firstConnectorEndpoint,h0,h1,
        edgeEquiv,finProdFinEquiv] <;> ring

theorem positive_secondConnector_endpoint {m k : ℕ} (hk : 3 ≤ k) (outer inner : ℕ)
    (t : Fin (m-1)) (j : Fin k) :
    serializedEndpoint outer inner
      ((positive m k hk).shape.ports ⟨vertexEquiv m (.inr (t,true)),j⟩) =
      ComputationLayout.secondConnectorEndpoint k inner t.val j.val := by
  change serializedEndpoint outer inner (positivePorts m k hk _) = _
  rw [positivePorts_named]
  simp [namedPorts,Equiv.coe_fn_mk,serializedEndpoint,ComputationLayout.secondConnectorEndpoint,
    edgeEquiv,finProdFinEquiv] <;> ring

theorem nullary_zero_endpoint (k outer inner : ℕ) (j : Fin k) :
    serializedEndpoint outer inner ((nullary k).shape.ports ⟨(0 : Fin 2),j⟩) = (inner+j.val,false) := by
  rw [nullary_port_zero]
  rfl

theorem nullary_one_endpoint (k outer inner : ℕ) (j : Fin k) :
    serializedEndpoint outer inner ((nullary k).shape.ports ⟨(1 : Fin 2),j⟩) = (inner+j.val,true) := by
  rw [nullary_port_one]
  rfl

end
end Paper2.DegreeCSP.EqualityTemplates
