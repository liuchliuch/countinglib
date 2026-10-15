import Counting.Reduction.OneQuery.Canonical

/-! # Uniqueness of complete charged oracle transcripts

This uses the existing oracle transition relation. A terminated run fixes every
transition, its charged cost and its ordered query/answer list.
-/

namespace Counting.Reduction.OneQuery
open PlanarHom.Complexity

theorem run_unique {m : OracleTM2} {oracle : Bits → Bits} {c d e : m.Cfg}
    {s t u v : ℕ} {qs rs : OracleTM2.Transcript}
    (h : m.Run oracle c d s t qs) (k : m.Run oracle c e u v rs)
    (hd : m.step oracle d = none) (he : m.step oracle e = none) :
    d = e ∧ s = u ∧ t = v ∧ qs = rs := by
  induction h generalizing e u v rs with
  | refl c =>
      cases k with
      | refl => exact ⟨rfl, rfl, rfl, rfl⟩
      | ordinary hn ht _ =>
          have hstep : m.step oracle c = m.core.tm.step c := by
            simp only [OracleTM2.step, hn]
          have impossible := hstep.trans ht
          rw [hd] at impossible
          contradiction
      | query next hq _ => simp [OracleTM2.step, hq] at hd
  | @ordinary c c' d s t qs hn ht hr ih =>
      cases k with
      | refl =>
          have hstep : m.step oracle c = some c' := by
            change (match m.continuation c with | none => m.core.tm.step c | some next => _) = _
            rw [hn]
            exact ht
          rw [hstep] at he
          contradiction
      | ordinary hn' ht' hr' =>
          have same := Option.some.inj (ht.symm.trans ht')
          subst same
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ih hr' hd he
          exact ⟨rfl, rfl, rfl, rfl⟩
      | query next hq _ => simp [hn] at hq
  | @query c d s t qs next hq hr ih =>
      cases k with
      | refl => simp [OracleTM2.step, hq] at he
      | ordinary hn _ _ => simp [hn] at hq
      | query next' hq' hr' =>
          have same := Option.some.inj (hq.symm.trans hq')
          subst next'
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ih hr' hd he
          exact ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem step_final (m : OracleTM2) (oracle : Bits → Bits) (answer : Bits) :
    m.step oracle (m.final answer) = none := by
  simp [OracleTM2.step, OracleTM2.continuation, OracleTM2.final,
    Turing.haltList, Turing.FinTM2.step, Turing.TM2.step]
  rfl

end Counting.Reduction.OneQuery
