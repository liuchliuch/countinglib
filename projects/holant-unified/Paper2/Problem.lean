import Paper2.ExactInput.FiniteLanguage
import Paper2.ExactInput.GraphSemantics
import Paper2.Complexity.ClosedNetworkCompleteness
import Paper2.Complexity.OracleQueryBounds

/-! The literal finite-language graph problem and exact finite-machine claims.
No answer or size function is a parameter of `value`. The graph parser checks
ordered ports and both ends of every edge; loops and nullaries are retained.
Root descriptors need not be unique. Hardness quantifies over every correct,
polynomial-length choice of descriptors and explicitly asserts one exists. -/
set_option backward.isDefEq.respectTransparency false

namespace Paper2.Problem
open Computability Paper2.Complexity Paper2.ExactInput Paper2.Tractable
open scoped BigOperators

inductive Wiring where
  | ordinary
  | nativeX
  deriving DecidableEq

noncomputable def Wiring.kernel : Wiring → Kernel AlgebraicComplex
  | .ordinary => Signature.equality
  | .nativeX => Signature.disequality

abbrev Instance (L : Language) :=
  { r : RawClosedNetwork // r.WellFormed L.count 1 L.arity }

def inputEncoding (L : Language) : Encoding (Instance L) Bool :=
  RawClosedNetwork.validatedEncoding L.count 1 L.arity

noncomputable def network (w : Wiring) (L : Language) (G : Instance L) : Network AlgebraicComplex 0 :=
  G.val.realize G.property L.signature (fun _ => w.kernel)

/-- The target answer is the exact finite sum of the literal input tables. -/
noncomputable def value (w : Wiring) (L : Language) (G : Instance L) : AlgebraicComplex :=
  (network w L G).denote Fin.elim0

/-- Ordinary Holant is one bit per edge with the original ordered incidence map.
Both occurrences of a loop read the very same edge bit. -/
theorem ordinary_value (L : Language) (G : Instance L) :
    value .ordinary L G =
      ∑ a : Fin G.val.edges.length → Bool,
        ∏ v : Fin G.val.vertices.length,
          L.signature (G.val.signatureLabel G.property v)
            (fun i => a (G.val.route G.property ⟨v, i⟩).1) := by
  change (Network.mk (G.val.shape G.property)
    (fun v => L.signature (G.val.signatureLabel G.property v))
    (fun _ => Signature.equality)).denote Fin.elim0 = _
  rw [Network.denote_equality]
  rfl

/-- Every graph's actual vertex/edge count is bounded by its faithful bit encoding. -/
theorem counts_le_input_length (L : Language) (G : Instance L) :
    G.val.vertices.length + G.val.edges.length ≤ ((inputEncoding L).encode G).length :=
  G.val.counts_le_encoded_length

/-- A zero vertex annihilates the actual answer; preprocessing cannot simply
remove it from an instance without retaining this case. -/
theorem value_zero_of_vertex (w : Wiring) (L : Language) (G : Instance L)
    (v : Fin G.val.vertices.length)
    (hz : L.signature (G.val.signatureLabel G.property v) = 0) : value w L G = 0 := by
  unfold value Network.denote
  apply Finset.sum_eq_zero
  intro z _
  have hp : (∏ u : Fin (network w L G).shape.vertices,
      (network w L G).vertex u ((network w L G).shape.assignment Fin.elim0 z u)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    change L.signature (G.val.signatureLabel G.property v) _ = 0
    rw [hz]
    rfl
  rw [hp, zero_mul]

/-- Correctness requires the strict public monic/irreducible isolated-root format. -/
def CorrectAnswers (w : Wiring) (L : Language) (answer : Instance L → RootCode) : Prop :=
  ∀ G, (answer G).MinimalRepresents (value w L G : ℂ)

/-- Actual deterministic finite TM2 evaluation in polynomial graph-bit time. -/
def InFP (w : Wiring) (L : Language) : Prop :=
  ∃ answer : Instance L → RootCode,
    CorrectAnswers w L answer ∧ Complexity.InFP (inputEncoding L) rootEncoding answer

/-- A valid public oracle answer convention with an actual polynomial bit bound.
This has mathematical content and is not supplied by classical decidability. -/
structure BoundedAnswers (w : Wiring) (L : Language) where
  answer : Instance L → RootCode
  correct : CorrectAnswers w L answer
  outputBound : PolynomialOutputBound (inputEncoding L) rootEncoding answer

/-- #P-hardness for the exact original graph problem. The existence conjunct
prevents a vacuous universal statement if bounded public answers are not yet proved.
The reduction includes actual run correctness, finite machines, valid graph queries,
query-length bounds and answer-length bounds. -/
def SharpPHard (w : Wiring) (L : Language) : Prop :=
  Nonempty (BoundedAnswers w L) ∧
    ∀ answers : BoundedAnswers w L, ∀ f : List Bool → ℕ,
      InSharpP (encodingList Bool) f →
        Nonempty (LengthControlledOracleReduction
          (encodingList Bool) encodingNatBool (inputEncoding L) rootEncoding f answers.answer)

/-- Every hardness assertion supplies a real bounded oracle interpretation. -/
theorem SharpPHard.nonvacuous {w : Wiring} {L : Language} (h : SharpPHard w L) :
    ∃ answer : Instance L → RootCode, CorrectAnswers w L answer ∧
      Nonempty (PolynomialOutputBound (inputEncoding L) rootEncoding answer) := by
  obtain ⟨a⟩ := h.1
  exact ⟨a.answer, a.correct, ⟨a.outputBound⟩⟩

/-- Source recognition is effective but is not claimed polynomial in the table list.
Only valid exact inputs need halt. The read tape is the literal descriptor-list bits. -/
structure TractRecognizer where
  decision : Language → Bool
  machine : Turing.TM2Computable Language.bits encodingBoolBool.encode decision
  finiteAlphabets : ∀ k, Fintype (machine.tm.Γ k)
  correct : ∀ L, decision L = true ↔ Tract L.family

end Paper2.Problem
