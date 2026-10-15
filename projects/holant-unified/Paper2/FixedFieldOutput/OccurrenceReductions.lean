import Paper2.FixedFieldOutput.Reductions
import Paper2.RelativeEO.TaggedExtension

/-! Designated-occurrence promises with unique canonical field-coordinate
answers. Promise proofs add no graph bits, and restrictions preserve every
actual transition and valid-query obligation. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Paper2.FixedFieldOutput
open Computability Paper2.Complexity Paper2.ExactInput Paper2.Problem Paper2.Tractable
open Paper2.RelativeEO

noncomputable def taggedAnswer (w : Wiring) (L : Language) {n : ℕ}
    (g : Signature AlgebraicComplex n) (p : ℕ → Prop) :
    TaggedInstance L g p → Answer (tagged L g) := fun G => answer w (tagged L g) G.val

noncomputable def taggedOutputBound (w : Wiring) (L : Language) {n : ℕ}
    (g : Signature AlgebraicComplex n) (p : ℕ → Prop) [DecidablePred p] :
    PolynomialOutputBound (taggedEncoding L g p) (answerEncoding (tagged L g))
      (taggedAnswer w L g p) where
  bound := (outputBound w (tagged L g)).bound
  length_le G := (outputBound w (tagged L g)).length_le G.val

def TaggedReduces (w : Wiring) (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (p : ℕ → Prop) [DecidablePred p] (target : Language) : Prop :=
  Nonempty (LengthControlledOracleReduction
    (taggedEncoding L g p) (answerEncoding (tagged L g))
    (inputEncoding target) (answerEncoding target)
    (taggedAnswer w L g p) (answer w target))

def sameInputReduction {α α' β γ δ : Type}
    {ea : Encoding α Bool} {ea' : Encoding α' Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}
    (r : LengthControlledOracleReduction ea eb ec ed f g)
    (toInput : α' → α) (bytes : ∀ a, ea.encode (toInput a) = ea'.encode a) :
    LengthControlledOracleReduction ea' eb ec ed (fun a => f (toInput a)) g where
  reduction := {
    machine := r.reduction.machine
    time := r.reduction.time
    correct := fun oracle ho a => by simpa only [bytes] using r.reduction.correct oracle ho (toInput a) }
  targetOutput := r.targetOutput
  queryBound := r.queryBound
  safeQuery := by
    intro oracle ho a t c hr hq
    have hr' : r.reduction.machine.run oracle (ea.encode (toInput a)) t = some c := by
      simpa only [bytes] using hr
    simpa only [bytes] using r.safeQuery oracle ho (toInput a) t c hr' hq

 theorem TaggedReduces.restrict {w : Wiring} {L target : Language} {n : ℕ}
    {g : Signature AlgebraicComplex n} {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (h : TaggedReduces w L g q target) (hpq : ∀ k, p k → q k) :
    TaggedReduces w L g p target := by
  obtain ⟨r⟩ := h
  let into : TaggedInstance L g p → TaggedInstance L g q :=
    fun G => ⟨G.val,hpq _ G.property⟩
  let r' := sameInputReduction (ea' := taggedEncoding L g p) r into (fun _ => rfl)
  change Nonempty (LengthControlledOracleReduction
    (taggedEncoding L g p) (answerEncoding (tagged L g))
    (inputEncoding target) (answerEncoding target)
    (fun G => taggedAnswer w L g q (into G)) (answer w target))
  exact ⟨r'⟩

 theorem TaggedReduces.exactly_one {w : Wiring} {L target : Language} {n : ℕ}
    {g : Signature AlgebraicComplex n} (h : TaggedReduces w L g (fun k => k ≤ 1) target) :
    TaggedReduces w L g (fun k => k = 1) target := h.restrict (fun _ hk => hk.le)

 theorem TaggedReduces.trans {w : Wiring} {L target next : Language} {n : ℕ}
    {g : Signature AlgebraicComplex n} {p : ℕ → Prop} [DecidablePred p]
    (h : TaggedReduces w L g p target) (ht : Reduces w target next) :
    TaggedReduces w L g p next := by
  obtain ⟨r⟩ := h
  obtain ⟨t⟩ := ht
  exact ⟨r.controlledCompose t⟩

end Paper2.FixedFieldOutput
