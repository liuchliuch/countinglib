import Paper2.NetworkSubstitution
import Paper2.Problem

/-! A list presentation of the literal native-X assignment sum, tied to the
validated original input evaluator. The graph-changing algorithms can operate
on raw rows while their semantic proof stays in the exact incidence model. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace Paper2.BellReduction.RawNative
open Complexity ExactInput Tractable Problem
variable {K : Type} [CommSemiring K]

/-- Invalid addresses receive a total default; well-formedness proves they
are never read by a valid instance. Edge orientation retains the X complement. -/
def readEnd {n : ℕ} (z : Fin n → Bool) (p : RawEndpoint) : Bool :=
  if h : p.1 < n then if p.2 then !(z ⟨p.1,h⟩) else z ⟨p.1,h⟩ else false

def rowValue {n : ℕ} (T : ℕ → List Bool → K) (z : Fin n → Bool) (v : RawVertex) : K :=
  T v.1 (v.2.map (readEnd z))

def evaluate (T : ℕ → List Bool → K) (G : RawClosedNetwork) : K :=
  ∑ z : Fin G.edges.length → Bool, (G.vertices.map (rowValue T z)).prod

/-- The actual fixed input table, read from a complete ordered list of bits.
The two validity tests only guard invalid raw syntax. -/
noncomputable def languageTable (L : Language) (a : ℕ) (xs : List Bool) : AlgebraicComplex :=
  if ha : a < L.count then
    if hx : xs.length = L.arity a then
      L.signature ⟨a,ha⟩ (fun i => xs.get (Fin.cast hx.symm i))
    else 0
  else 0

theorem languageTable_row (L : Language) (G : Instance L)
    (z : Fin G.val.edges.length → Bool) (v : Fin G.val.vertices.length) :
    rowValue (languageTable L) z (G.val.vertices.get v) =
      L.signature (G.val.signatureLabel G.property v)
        (fun i => readEnd z (G.val.portEndpoint G.property ⟨v,i⟩)) := by
  have ha := (G.property.1 v).1
  have hx : ((G.val.vertices.get v).2.map (readEnd z)).length =
      L.arity (G.val.vertices.get v).1 := by simpa using (G.property.1 v).2
  simp only [rowValue,languageTable,dif_pos ha,dif_pos hx]
  apply congrArg (L.signature (G.val.signatureLabel G.property v))
  funext i
  simp [RawClosedNetwork.portEndpoint]

theorem readEnd_route (L : Language) (G : Instance L)
    (z : Fin G.val.edges.length → Bool) (p : G.val.Ports L.arity) :
    readEnd z (G.val.portEndpoint G.property p) =
      if (G.val.route G.property p).2 then !(z (G.val.route G.property p).1)
      else z (G.val.route G.property p).1 := by
  simp only [readEnd,dif_pos (G.val.portEndpoint_bound G.property p)]
  rfl

/-- The list sum is exactly the public original-language native-X evaluator.
No graph, label, port order, loop, nullary vertex or scalar is abstracted away. -/
theorem evaluate_language (L : Language) (G : Instance L) :
    evaluate (K := AlgebraicComplex) (languageTable L) G.val = Problem.value .nativeX L G := by
  unfold evaluate value
  rw [Network.denote_nativeX _ (fun _ => rfl)]
  apply Finset.sum_congr rfl
  intro z _
  have hp : (G.val.vertices.map (rowValue (languageTable L) z)).prod =
      ∏ v : Fin G.val.vertices.length, rowValue (languageTable L) z (G.val.vertices.get v) := by
    rw [← List.prod_ofFn]
    congr 1
    exact (List.ofFn_getElem_eq_map _ _).symm
  rw [hp]
  apply Finset.prod_congr rfl
  intro v _
  rw [languageTable_row]
  change L.signature (G.val.signatureLabel G.property v)
      (fun i => readEnd z (G.val.portEndpoint G.property ⟨v,i⟩)) =
    L.signature (G.val.signatureLabel G.property v)
      (fun i => if (G.val.route G.property ⟨v,i⟩).2 then
        !(z (G.val.route G.property ⟨v,i⟩).1) else z (G.val.route G.property ⟨v,i⟩).1)
  apply congrArg (L.signature (G.val.signatureLabel G.property v))
  funext i
  rw [readEnd_route]

end Paper2.BellReduction.RawNative
