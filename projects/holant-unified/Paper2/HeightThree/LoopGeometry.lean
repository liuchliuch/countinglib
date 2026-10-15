import Paper2.NetworkRealization
import Paper2.Certificates.Q6Action

/-! Literal six-port mountain coordinates and the fifteen native-X loops. -/
namespace Paper2.HeightThree
open Certificates.Q6
open scoped BigOperators

def occupied {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => x v = true)

def subsetWord (S : PortSet) : Port → Bool := fun v => decide (v ∈ S)

lemma occupied_subsetWord (S : PortSet) : occupied (subsetWord S) = S := by
  ext v
  simp [occupied,subsetWord]

lemma subsetWord_occupied (x : Port → Bool) : subsetWord (occupied x) = x := by
  funext v
  simp [occupied,subsetWord]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma occupied_card_weight (x : Port → Bool) : (occupied x).card = weight x := by
  revert x
  decide +kernel

def loopPlacement (i : Fin 15) : Fin 4 ⊕ Bool → Port :=
  Sum.elim (loopSpecs i).residual (fun t => if t then (loopSpecs i).second else (loopSpecs i).first)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma loopPlacement_bijective (i : Fin 15) : Function.Bijective (loopPlacement i) := by
  revert i
  decide +kernel

noncomputable def loopPortEquiv (i : Fin 15) : Port ≃ (Fin 4 ⊕ Bool) :=
  (Equiv.ofBijective (loopPlacement i) (loopPlacement_bijective i)).symm

/-- All bits, including the two opposing internal ports, are retained. -/
def loopWord (i : Fin 15) (x : Fin 4 → Bool) (t : Bool) : Port → Bool := fun v =>
  if v = (loopSpecs i).first then t
  else if v = (loopSpecs i).second then !t
  else decide (∃ j : Fin 4, (loopSpecs i).residual j = v ∧ x j = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma loopWord_placement (i : Fin 15) (x : Fin 4 → Bool) (t : Bool) (z : Fin 4 ⊕ Bool) :
    loopWord i x t (loopPlacement i z) = Sum.elim x (fun b => if b then !t else t) z := by
  revert i x t z
  decide +kernel

lemma loopWord_assignment (i : Fin 15) (x : Fin 4 → Bool) (t : Bool) :
    (fun v => Sum.elim x (fun b => if b then !t else t) (loopPortEquiv i v)) = loopWord i x t := by
  funext v
  obtain ⟨z,rfl⟩ := (loopPlacement_bijective i).2 v
  rw [loopWord_placement]
  change Sum.elim x _ ((Equiv.ofBijective _ (loopPlacement_bijective i)).symm
    ((Equiv.ofBijective _ (loopPlacement_bijective i)) z)) = _
  rw [Equiv.symm_apply_apply]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma loopWord_weight (i : Fin 15) (x : Fin 4 → Bool) (t : Bool) :
    weight (loopWord i x t) = weight x + 1 := by
  revert i x t
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma loopWord_not_constant (i : Fin 15) (x : Fin 4 → Bool) (t b : Bool) :
    loopWord i x t ≠ (fun _ => b) := by
  revert i x t b
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma loopWord_occupied (i : Fin 15) (e : Fin 6) (t : Bool) :
    occupied (loopWord i (eoWords e) t) =
      insert (if t then (loopSpecs i).first else (loopSpecs i).second)
        (loopChosen (loopSpecs i) e) := by
  revert i e t
  decide +kernel

variable {K : Type} [CommSemiring K]

/-- Exactly aδ₀+bδ₁+Q, Q supported on the twenty triples. -/
def coordinateMountain (a b : K) (q : Fin 20 → K) : Signature K 6 := fun x =>
  (if x = (fun _ => false) then a else 0) +
  (if x = (fun _ => true) then b else 0) + coefficient q (mask (occupied x))

def loopSignature (M : Signature K 6) (i : Fin 15) : Signature K 4 := fun x =>
  ∑ t : Bool, M (loopWord i x t)

lemma loopSignature_contract (M : Signature K 6) (i : Fin 15) :
    Tensor.contractX (Tensor.reindex (loopPortEquiv i) M) = loopSignature M i := by
  funext x
  unfold Tensor.contractX Tensor.reindex loopSignature
  apply Finset.sum_congr rfl
  intro t _
  rw [loopWord_assignment]

lemma loopSignature_realizable (F : SignatureFamily K) (M : Signature K 6)
    (hM : NetworkRealizable F M) (i : Fin 15) : NetworkRealizable F (loopSignature M i) := by
  rw [← loopSignature_contract]
  exact (hM.reindex (loopPortEquiv i)).selfLoop

lemma loopSignature_array (a b : K) (q : Fin 20 → K) (i : Fin 15) (e : Fin 6) :
    loopSignature (coordinateMountain a b q) i (eoWords e) = loopArray q (loopSpecs i) e := by
  unfold loopSignature coordinateMountain
  simp only [loopWord_not_constant,ite_false,zero_add,Fintype.sum_bool,loopWord_occupied]
  simp only [ite_true,Bool.false_eq_true,ite_false]
  rfl

end Paper2.HeightThree
