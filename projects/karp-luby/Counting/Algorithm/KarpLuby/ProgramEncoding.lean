import Counting.Algorithm.KarpLuby.Program
import Counting.Algorithm.KarpLuby.Encoding

/-!
# A total binary request evaluator

The input word contains the complete explicit DNF, two binary rationals, and
one finite Boolean tape. Parsing validates variable indices and denominators.
Evaluation additionally checks the admissible accuracy range and exact tape
length. Malformed or invalid requests return the encoded rational zero. The
function is executable Lean; no finite-machine running-time claim is made.
-/

namespace Counting.Algorithm.KarpLuby.ProgramEncoding

open DNF

/-- A parsed request still has to pass accuracy and exact-tape-length validation. -/
structure Request where
  problem : Encoding.Input
  epsilon : ℚ
  delta : ℚ
  tape : List Bool

/-- Each component is explicitly serialized; no natural or rational value is an atom. -/
def request : Encoding.BitEncoding Request :=
  Encoding.retract
    (Encoding.prod Encoding.input
      (Encoding.prod Encoding.output (Encoding.prod Encoding.output Encoding.bits)))
    (fun r => (r.problem, (r.epsilon, (r.delta, r.tape))))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩)
    (by intro r; cases r; rfl)

instance (epsilon delta : ℚ) : Decidable (Program.ValidRequest epsilon delta) :=
  inferInstanceAs (Decidable (0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < delta ∧ delta < 1))

/-- Invalid accuracy values and wrong tape lengths terminate with zero. -/
def evalRequest (r : Request) : ℚ :=
  if Program.ValidRequest r.epsilon r.delta then
    if h : r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta then
      Program.run r.problem.formula r.epsilon r.delta
        (fun i => r.tape[i.val]'(by omega))
    else 0
  else 0

/-- A total deterministic evaluator on a fixed finite alphabet. -/
def evalBits (s : List Bool) : List Bool :=
  Encoding.encodeOutput (match request.decode s with
    | none => 0
    | some r => evalRequest r)

/-- Assemble the canonical request from an exactly sized random tape. -/
def ofRun {n : ℕ} (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) : Request :=
  ⟨⟨n, f⟩, epsilon, delta, List.ofFn tape⟩

def encodeRun {n : ℕ} (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) : List Bool :=
  request.encode (ofRun f epsilon delta tape)

@[simp] theorem ofRun_tape_length {n : ℕ} (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    (ofRun f epsilon delta tape).tape.length = Program.requestedBudget f epsilon delta := by
  simp [ofRun]

@[simp] theorem decode_encodeRun {n : ℕ} (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    request.decode (encodeRun f epsilon delta tape) = some (ofRun f epsilon delta tape) :=
  request.decode_encode _

theorem evalRequest_ofRun {n : ℕ} (f : Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    evalRequest (ofRun f epsilon delta tape) = Program.run f epsilon delta tape := by
  simp [evalRequest, ofRun, hvalid]

/-- The binary evaluator computes precisely the verified rational estimator. -/
theorem evalBits_encodeRun {n : ℕ} (f : Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    evalBits (encodeRun f epsilon delta tape) =
      Encoding.encodeOutput (Program.run f epsilon delta tape) := by
  simp [evalBits, evalRequest_ofRun f epsilon delta hvalid tape]

/-- End-to-end decoding correctness for the binary program boundary. -/
theorem decode_evalBits_encodeRun {n : ℕ} (f : Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    Encoding.decodeOutput (evalBits (encodeRun f epsilon delta tape)) =
      some (Program.run f epsilon delta tape) := by
  rw [evalBits_encodeRun f epsilon delta hvalid tape, Encoding.decode_encodeOutput]

theorem evalRequest_invalid (r : Request) (h : ¬ Program.ValidRequest r.epsilon r.delta) :
    evalRequest r = 0 := by simp [evalRequest, h]

theorem evalRequest_wrong_length (r : Request)
    (h : r.tape.length ≠ Program.requestedBudget r.problem.formula r.epsilon r.delta) :
    evalRequest r = 0 := by
  unfold evalRequest
  split_ifs <;> simp_all

theorem evalBits_malformed (s : List Bool) (h : request.decode s = none) :
    evalBits s = Encoding.encodeOutput 0 := by simp [evalBits, h]

/-- Every result word is a valid rational encoding, even for malformed requests. -/
theorem evalBits_decodes (s : List Bool) : ∃ q : ℚ,
    Encoding.decodeOutput (evalBits s) = some q := by
  unfold evalBits
  exact ⟨_, Encoding.decode_encodeOutput _⟩

end Counting.Algorithm.KarpLuby.ProgramEncoding
