import Paper2.RelativeEO.TaggedExtension
import Paper2.ExactInput.UnconditionalTransport

/-! Actual finite-machine reductions on designated-occurrence promises.
Restriction keeps the raw source bytes, machine, polynomial, valid queries, and
query-length bounds. It does not decide semantic equality of signature values. -/
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.Complexity Computability

/-- Source-type reinterpretation for a controlled oracle machine. Every actual
run is unchanged, including all prefix query-validity and length obligations. -/
def sameInputReduction {α α' β γ δ : Type}
    {ea : Encoding α Bool} {ea' : Encoding α' Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}
    (r : LengthControlledOracleReduction ea eb ec ed f g)
    (toInput : α' → α) (sameBytes : ∀ a, ea.encode (toInput a) = ea'.encode a) :
    LengthControlledOracleReduction ea' eb ec ed (fun a => f (toInput a)) g where
  reduction := {
    machine := r.reduction.machine
    time := r.reduction.time
    correct := fun oracle ho a => by simpa only [sameBytes] using r.reduction.correct oracle ho (toInput a) }
  targetOutput := r.targetOutput
  queryBound := r.queryBound
  safeQuery := by
    intro oracle ho a t c hr hq
    have hr' : r.reduction.machine.run oracle (ea.encode (toInput a)) t = some c := by
      simpa only [sameBytes] using hr
    simpa only [sameBytes] using r.safeQuery oracle ho (toInput a) t c hr' hq

@[simp] theorem sameInputReduction_machine {α α' β γ δ : Type}
    {ea : Encoding α Bool} {ea' : Encoding α' Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}
    (r : LengthControlledOracleReduction ea eb ec ed f g)
    (toInput : α' → α) (sameBytes : ∀ a, ea.encode (toInput a) = ea'.encode a) :
    (sameInputReduction r toInput sameBytes).reduction.machine = r.reduction.machine := rfl

structure TaggedBoundedAnswers (w : Wiring) (L : Language) {n : ℕ}
    (g : Signature AlgebraicComplex n) (p : ℕ → Prop) [DecidablePred p] where
  answer : TaggedInstance L g p → RootCode
  correct : ∀ G, (answer G).MinimalRepresents (value w (tagged L g) G.val : ℂ)
  outputBound : PolynomialOutputBound (taggedEncoding L g p) rootEncoding answer

def TaggedReduces (w : Wiring) (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (p : ℕ → Prop) [DecidablePred p] (target : Language) : Prop :=
  ∀ targetAnswers : BoundedAnswers w target,
    ∃ sourceAnswers : TaggedBoundedAnswers w L g p,
      Nonempty (LengthControlledOracleReduction
        (taggedEncoding L g p) rootEncoding (inputEncoding target) rootEncoding
        sourceAnswers.answer targetAnswers.answer)

/-- Promise restriction preserves public output bounds as a theorem. -/
noncomputable def taggedBoundedAnswers (w : Wiring) (L : Language) {n : ℕ}
    (g : Signature AlgebraicComplex n) (p : ℕ → Prop) [DecidablePred p] :
    TaggedBoundedAnswers w L g p where
  answer G := (publicBoundedAnswers w (tagged L g)).answer G.val
  correct G := (publicBoundedAnswers w (tagged L g)).correct G.val
  outputBound := {
    bound := (publicBoundedAnswers w (tagged L g)).outputBound.bound
    length_le := fun G => (publicBoundedAnswers w (tagged L g)).outputBound.length_le G.val }

/-- This is actual encoded input restriction, not a new reduction assumption. -/
theorem TaggedReduces.restrict {w : Wiring} {L target : Language} {n : ℕ}
    {g : Signature AlgebraicComplex n} {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (h : TaggedReduces w L g q target) (hpq : ∀ k, p k → q k) :
    TaggedReduces w L g p target := by
  intro targetAnswers
  obtain ⟨a, ⟨r⟩⟩ := h targetAnswers
  let into : TaggedInstance L g p → TaggedInstance L g q :=
    fun G => ⟨G.val, hpq _ G.property⟩
  let b : TaggedBoundedAnswers w L g p := {
    answer := fun G => a.answer (into G)
    correct := fun G => a.correct (into G)
    outputBound := { bound := a.outputBound.bound, length_le := fun G => a.outputBound.length_le (into G) } }
  exact ⟨b, ⟨sameInputReduction r into (fun _ => rfl)⟩⟩

/-- Exactly-one inputs inherit the universal at-most-one reduction on identical
bytes. In particular an existing source label denoting g is not counted twice. -/
theorem TaggedReduces.exactly_one {w : Wiring} {L target : Language} {n : ℕ}
    {g : Signature AlgebraicComplex n}
    (h : TaggedReduces w L g (fun k => k ≤ 1) target) :
    TaggedReduces w L g (fun k => k = 1) target :=
  h.restrict (fun _ hk => hk.le)

/-- Promised source reductions compose with ordinary retained-language reductions
using the already verified finite oracle inliner and polynomial query bounds. -/
theorem TaggedReduces.trans {w : Wiring} {L target next : Language} {n : ℕ}
    {g : Signature AlgebraicComplex n} {p : ℕ → Prop} [DecidablePred p]
    (h : TaggedReduces w L g p target) (ht : Reduces w target next) :
    TaggedReduces w L g p next := by
  intro nextAnswers
  obtain ⟨targetAnswers, ⟨rt⟩⟩ := ht nextAnswers
  obtain ⟨sourceAnswers, ⟨rs⟩⟩ := h targetAnswers
  exact ⟨sourceAnswers, ⟨rs.controlledCompose rt⟩⟩

end Paper2.RelativeEO
