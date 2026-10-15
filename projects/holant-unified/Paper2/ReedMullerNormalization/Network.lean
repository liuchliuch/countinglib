import Paper2.ReedMullerNormalization.Endpoint
import Paper2.NetworkSubstitution

/-! The endpoint-repair sum is an actual two-source graph: four native-X
edges join the printed information sets, and a fifth closes the first boundary
pair. Both vertices retain the original eight-port signature. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.ReedMullerNormalization
open ReedMuller

 def repairPort (v : Bool) (i : Fin 8) : Fin 8 ⊕ (Fin 4 × Bool) :=
  ![Sum.inr (0,v),Sum.inr (3,v),Sum.inr (2,v),Sum.inl (if v then 1 else 0),
    Sum.inr (1,v),Sum.inl (if v then 3 else 2),Sum.inl (if v then 5 else 4),
    Sum.inl (if v then 7 else 6)] i

 def repairPortInv : Fin 8 ⊕ (Fin 4 × Bool) → (Σ _ : Bool, Fin 8)
  | .inl i => ![⟨false,3⟩,⟨true,3⟩,⟨false,5⟩,⟨true,5⟩,
      ⟨false,6⟩,⟨true,6⟩,⟨false,7⟩,⟨true,7⟩] i
  | .inr (i,v) => ⟨v,(![0,4,2,1] : Fin 4 → Fin 8) i⟩

 def repairPorts : (Σ _ : Bool, Fin 8) ≃ Fin 8 ⊕ (Fin 4 × Bool) where
  toFun p := repairPort p.1 p.2
  invFun := repairPortInv
  left_inv := by decide +kernel
  right_inv := by decide +kernel

 noncomputable def repairFiniteNetwork {K : Type} [CommSemiring K] (M : Signature K 8) :
    FiniteNetwork K Bool (Fin 4) 8 where
  arity := fun _ => 8
  ports := repairPorts
  vertex := fun _ => M
  edge := fun _ => Signature.disequality

 theorem repair_assignment (x : Fin 8 → Bool) (z : Fin 4 → Bool) (v : Bool) :
    (fun i => Sum.elim x (fun p : Fin 4 × Bool => if p.2 then !(z p.1) else z p.1)
      (repairPort v i)) =
        if v then join (compl z) ![x 1,x 3,x 5,x 7]
        else join z ![x 0,x 2,x 4,x 6] := by
  cases v <;> funext i <;> fin_cases i <;> rfl

 theorem repairFiniteNetwork_denote {K : Type} [CommRing K] (A B c : K) :
    (repairFiniteNetwork (source A B c)).denote = eightOutput A B c := by
  classical
  funext x
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  rw [eightOutput,joined_eliminate_edges]
  refine Finset.sum_congr (by ext z; simp) ?_
  intro z _
  rw [Fintype.prod_bool]
  simp only [repairFiniteNetwork,repairPorts,Equiv.coe_fn_mk,repair_assignment,
    Bool.false_eq_true,ite_false,ite_true]
  ring

 noncomputable def repairNetwork {K : Type} [CommRing K] (M : Signature K 8) : Network K 6 :=
  (repairFiniteNetwork M).toNetwork.contract Signature.disequality

 theorem repairNetwork_denote {K : Type} [CommRing K] (A B c : K) :
    (repairNetwork (source A B c)).denote = sixOutput A B c := by
  rw [repairNetwork,Network.denote_contract,FiniteNetwork.denote_toNetwork,repairFiniteNetwork_denote]
  exact congrArg (fun E => Signature.contract E (eightOutput A B c)) Bell.X_eq_disequality.symm

 theorem repairNetwork_uses {K : Type} [CommRing K] (M : Signature K 8)
    (F : SignatureFamily K) (hM : (⟨8,M⟩ : AnySignature K) ∈ F) :
    (repairNetwork M).Uses F := by
  apply Network.Uses.contract
  intro v
  exact hM

 theorem repairNetwork_nativeX {K : Type} [CommRing K] (M : Signature K 8) :
    (repairNetwork M).NativeX := by
  apply Network.NativeX.contract
  intro e
  rfl

 theorem repairNetwork_sizes {K : Type} [CommRing K] (M : Signature K 8) :
    (repairNetwork M).shape.vertices = 2 ∧ (repairNetwork M).shape.edges = 5 := by
  simp [repairNetwork,Network.contract,repairFiniteNetwork,FiniteNetwork.toNetwork]

 theorem sixOutput_realizable {K : Type} [CommRing K] (A B c : K)
    (F : SignatureFamily K) (hM : (⟨8,source A B c⟩ : AnySignature K) ∈ F) :
    NetworkRealizable F (sixOutput A B c) := by
  exact (repairNetwork_denote A B c) ▸
    ⟨6,repairNetwork (source A B c),Equiv.refl _,
      repairNetwork_uses _ F hM,repairNetwork_nativeX _,rfl⟩

end Paper2.ReedMullerNormalization
