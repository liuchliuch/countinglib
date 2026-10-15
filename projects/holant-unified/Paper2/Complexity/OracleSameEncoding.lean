import Paper2.Complexity.OracleQueryBounds

/-! Reinterpretation of the very same oracle-query bytes.  The program, every
transition, query polynomial and answer polynomial are preserved.  The semantic
equivalence is used only in the proof; no oracle or machine computes it. -/
namespace Paper2.Complexity
open Computability

namespace LengthControlledOracleReduction

/-- A byte-preserving bijection of target instances changes no machine work. -/
noncomputable def sameTarget {α β γ γ' δ : Type}
    {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ec' : Encoding γ' Bool} {ed : Encoding δ Bool}
    {f : α → β} {g : γ → δ} {g' : γ' → δ}
    (r : LengthControlledOracleReduction ea eb ec ed f g)
    (e : γ ≃ γ') (bytes : ∀ q, ec'.encode (e q) = ec.encode q)
    (answers : ∀ q, g' (e q) = g q) :
    LengthControlledOracleReduction ea eb ec' ed f g' where
  reduction := {
    machine := r.reduction.machine
    time := r.reduction.time
    correct := fun oracle h a => r.reduction.correct oracle
      (fun q => by rw [← bytes q, h (e q), answers q]) a }
  targetOutput := {
    bound := r.targetOutput.bound
    length_le := fun q => by
      have h := r.targetOutput.length_le (e.symm q)
      rw [← answers, Equiv.apply_symm_apply] at h
      simpa only [← bytes, Equiv.apply_symm_apply] using h }
  queryBound := r.queryBound
  safeQuery := by
    intro oracle h a t c run query
    obtain ⟨q, hq, hlen⟩ := r.safeQuery oracle
      (fun q => by rw [← bytes q, h (e q), answers q]) a t c run query
    exact ⟨e q, hq.trans (bytes q).symm, hlen⟩

@[simp] theorem sameTarget_machine {α β γ γ' δ : Type}
    {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ec' : Encoding γ' Bool} {ed : Encoding δ Bool}
    {f : α → β} {g : γ → δ} {g' : γ' → δ}
    (r : LengthControlledOracleReduction ea eb ec ed f g)
    (e : γ ≃ γ') (bytes : ∀ q, ec'.encode (e q) = ec.encode q)
    (answers : ∀ q, g' (e q) = g q) :
    (r.sameTarget e bytes answers).reduction.machine = r.reduction.machine := rfl

@[simp] theorem sameTarget_time {α β γ γ' δ : Type}
    {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ec' : Encoding γ' Bool} {ed : Encoding δ Bool}
    {f : α → β} {g : γ → δ} {g' : γ' → δ}
    (r : LengthControlledOracleReduction ea eb ec ed f g)
    (e : γ ≃ γ') (bytes : ∀ q, ec'.encode (e q) = ec.encode q)
    (answers : ∀ q, g' (e q) = g q) :
    (r.sameTarget e bytes answers).reduction.time = r.reduction.time := rfl

end LengthControlledOracleReduction
end Paper2.Complexity
