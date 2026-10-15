import Paper2.RelativeEO.TaggedExtension
import Paper2.ExactInput.InstanceSemantics
import Paper2.NetworkContraction

/-! The ordered directed pair Δ₀⊗Δ₁ and its literal one-vertex, one-loop
nonzero closure. The graph really contains exactly one designated Δ vertex. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation
open Paper2.Problem Paper2.Complexity

noncomputable def directedPair : Signature AlgebraicComplex 2 :=
  fun x => if x 0 = false ∧ x 1 = true then 1 else 0

theorem directedPair_ne_zero : directedPair ≠ 0 := by
  intro h
  have hx := congrFun h (fun i => i == 1)
  simp [directedPair] at hx

@[simp] theorem tagged_signature_zero (L : Language) {n : ℕ}
    (g : Signature AlgebraicComplex n) :
    (tagged L g).signature ⟨0, by rw [tagged_count]; omega⟩ = g := by
  change (codeOf g).denote (codeOf_valid g) = g
  exact codeOf_denote g

noncomputable def directedPairClosureNetwork : Network AlgebraicComplex 0 :=
  (Network.corolla directedPair).contract Signature.disequality

@[simp] theorem directedPairClosureNetwork_value :
    directedPairClosureNetwork.denote Fin.elim0 = 1 := by
  rw [directedPairClosureNetwork, Network.denote_contract, Network.denote_corolla]
  rw [Signature.contract_disequality]
  simp [directedPair, Fin.cons]
  rfl

noncomputable def directedPairClosureLabels (L : Language) :
    ClosedLabelling directedPairClosureNetwork.shape (tagged L directedPair).count 1
      (tagged L directedPair).arity where
  vertex _ := ⟨0, by rw [tagged_count]; omega⟩
  vertex_arity _ := rfl
  edge _ := 0

noncomputable def directedPairClosure (L : Language) : Instance (tagged L directedPair) :=
  serializeInstance _ (directedPairClosureLabels L)

@[simp] theorem directedPairClosure_occurrences (L : Language) :
    occurrenceCount (directedPairClosure L).val = 1 := by
  rfl

@[simp] theorem directedPairClosure_value (L : Language) :
    value .nativeX (tagged L directedPair) (directedPairClosure L) = 1 := by
  rw [directedPairClosure, value_serialize]
  have he : ((directedPairClosureLabels L).sourceNetwork
      (tagged L directedPair).signature (fun _ => Wiring.nativeX.kernel)) =
      directedPairClosureNetwork := by
    unfold ClosedLabelling.sourceNetwork
    congr 1
    · funext v x
      change (tagged L directedPair).signature ⟨0, _⟩ x = directedPair x
      exact congrFun (tagged_signature_zero L directedPair) x
    · funext e
      have he : e = (0 : Fin 1) := Fin.eq_zero e
      subst e
      rfl
  rw [he, directedPairClosureNetwork_value]

/-- A concrete legal promised input, not an assumed nonzero closed evaluation. -/
noncomputable def directedPairOneClosure (L : Language) :
    TaggedInstance L directedPair (fun k => k = 1) :=
  ⟨directedPairClosure L, directedPairClosure_occurrences L⟩

end Paper2.RelativeEO
