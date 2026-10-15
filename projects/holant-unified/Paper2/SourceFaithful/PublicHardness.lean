import Paper2.Complexity.ControlledCompose
import Paper2.Complexity.MachineRename
import Paper2.TractableAlgorithms.PublicEvaluation
import Paper2.ExactInput.FixedRootCodec.ReverseRootCodec

/-! Public strict-root hardness uses one identity graph query followed by an
executed finite root-to-coordinate decoder. The adapter works for every correct
bounded answer convention, including root descriptions outside the image of the
forward converter. Query safety is proved on every actual run prefix. -/
namespace Paper2.Complexity.OracleDecode
open Turing Computability BinaryCompose
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev machine (m : BinaryCompose.Machine) : OracleMachine where
  K := m.K
  inputStack := m.input
  outputStack := m.output
  queryStack := m.input
  answerStack := m.input
  Λ := Unit ⊕ m.Label
  main := Sum.inl ()
  σ := m.State
  initialState := m.initial
  program
    | .inl _ => .query (fun _ => .inr m.main)
    | .inr l => .ordinary (MachineRename.stmt (Equiv.refl m.K)
        Sum.inr (Equiv.refl m.State) (m.program l))

def lift (m : BinaryCompose.Machine) (c : m.Config) : (machine m).Cfg :=
  MachineRename.cfg (Equiv.refl m.K) Sum.inr (Equiv.refl m.State) c

theorem query_step (m : BinaryCompose.Machine) (oracle : List Bool → List Bool)
    (input : List Bool) :
    (machine m).step oracle ((machine m).init input) =
      some (lift m (initList m.computer (oracle input))) := by
  rw [m.init_eq]
  simp only [machine, OracleMachine.step, OracleMachine.init, lift, MachineRename.cfg,
    Equiv.refl_apply, Equiv.refl_symm, Function.comp_def, Option.map_some,
    wordTape]
  congr 2
  funext k
  by_cases hk : k = m.input <;> simp [hk]

theorem lift_halt (m : BinaryCompose.Machine) (word : List Bool) :
    lift m (haltList m.computer word) = (machine m).output word := by
  rw [m.halt_eq]
  simp only [lift, MachineRename.cfg, machine, OracleMachine.output,
    Equiv.refl_apply, Equiv.refl_symm, Function.comp_def, Option.map_none, wordTape]
  congr 1
  funext k
  by_cases hk : k = m.output <;> simp [hk]

theorem lift_step (m : BinaryCompose.Machine) (oracle : List Bool → List Bool)
    (c d : m.Config) (h : m.computer.step c = some d) :
    (machine m).step oracle (lift m c) = some (lift m d) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
    have hd : TM2.stepAux (m.program l) state tapes = d := Option.some.inj h
    subst d
    simpa [lift, machine, MachineRename.cfg, OracleMachine.step] using
      congrArg some (MachineRename.stepAux_stmt (Equiv.refl m.K) Sum.inr
        (Equiv.refl m.State) (m.program l) state tapes)

theorem lift_run (m : BinaryCompose.Machine) (oracle : List Bool → List Bool)
    (c d : m.Config) (n : ℕ)
    (h : (fun p => p.bind m.computer.step)^[n] (some c) = some d) :
    (fun p => p.bind ((machine m).step oracle))^[n] (some (lift m c)) =
      some (lift m d) := by
  change (fun p => p.bind (TM2.step m.program))^[n] (some c) = some d at h
  induction n generalizing d with
  | zero => have hd := Option.some.inj h; subst d; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (TM2.step m.program))^[n] (some c) with
    | none => simp [hp] at h
    | some previous =>
      have hs : m.computer.step previous = some d := by simpa [hp] using h
      rw [Function.iterate_succ_apply', ih previous hp]
      exact lift_step m oracle previous d hs

def outputs (m : BinaryCompose.Machine) (oracle : List Bool → List Bool)
    (input output : List Bool) (time : ℕ)
    (h : TM2OutputsInTime m.computer (oracle input) (some output) time) :
    (machine m).OutputsInTime oracle input output (time + 1) where
  steps := h.steps + 1
  evals_in_steps := by
    change (fun p => p.bind ((machine m).step oracle))^[h.steps+1]
      (some ((machine m).init input)) = some ((machine m).output output)
    rw [Function.iterate_add_apply, Function.iterate_one, Option.bind_some, query_step]
    rw [← lift_halt m output]
    exact lift_run m oracle _ _ h.steps h.evals_in_steps
  steps_le_m := Nat.add_le_add_right h.steps_le_m 1

theorem lift_not_query (m : BinaryCompose.Machine) (c : m.Config) :
    (lift m c).l ≠ some (.inl ()) := by
  cases c.l <;> simp [lift, MachineRename.cfg]

theorem step_not_query (m : BinaryCompose.Machine) (oracle : List Bool → List Bool)
    (c : (machine m).Cfg) :
    ((machine m).step oracle c).map (fun d => d.l) ≠ some (some (.inl ())) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => simp [OracleMachine.step]
  | some l =>
    cases l with
    | inl u => cases u; simp [OracleMachine.step, machine]
    | inr l =>
      have hs := MachineRename.stepAux_stmt (Equiv.refl m.K) (Sum.inr : m.Label → Unit ⊕ m.Label)
        (Equiv.refl m.State) (m.program l) state tapes
      have hn := lift_not_query m (TM2.stepAux (m.program l) state tapes)
      simp only [OracleMachine.step, machine, Option.map_some]
      change some (TM2.stepAux _ state tapes).l ≠ some (some (Sum.inl ()))
      have hs' : TM2.stepAux (MachineRename.stmt (Equiv.refl m.K)
          (Sum.inr : m.Label → Unit ⊕ m.Label) (Equiv.refl m.State) (m.program l))
          state tapes = lift m (TM2.stepAux (m.program l) state tapes) := by
        simpa only [Equiv.refl_apply, Equiv.refl_symm, Function.comp_def, lift] using hs
      rw [hs']
      exact fun he => hn (Option.some.inj he)

theorem isQuery_iff (m : BinaryCompose.Machine) (c : (machine m).Cfg) :
    (machine m).IsQuery c ↔ c.l = some (.inl ()) := by
  constructor
  · rintro ⟨l, next, hl, hp⟩
    cases l with
    | inl u => cases u; exact hl
    | inr l => simp [machine] at hp
  · intro h
    exact ⟨.inl (), (fun _ => .inr m.main), h, rfl⟩

theorem query_is_initial (m : BinaryCompose.Machine) (oracle : List Bool → List Bool)
    (input : List Bool) (t : ℕ) (c : (machine m).Cfg)
    (hrun : (machine m).run oracle input t = some c) (hq : (machine m).IsQuery c) :
    c = (machine m).init input := by
  cases t with
  | zero => exact (Option.some.inj hrun).symm
  | succ t =>
    rw [OracleMachine.run_succ] at hrun
    cases hp : (machine m).run oracle input t with
    | none => simp [hp] at hrun
    | some previous =>
      have hs : (machine m).step oracle previous = some c := by simpa [hp] using hrun
      have hn := step_not_query m oracle previous
      rw [hs] at hn
      exact False.elim (hn (congrArg some ((isQuery_iff m c).mp hq)))

variable {α β δ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ed : Encoding δ Bool} {f : α → β} {g : α → δ} {decode : δ → β}

/-- One actual query of the original input, then ordinary finite decoding. -/
def reduction (w : Computes ed eb decode) (size : PolynomialOutputBound ea ed g)
    (h : ∀ a, decode (g a) = f a) :
    LengthControlledOracleReduction ea eb ea ed f g where
  reduction := {
    machine := machine w.machine
    time := w.time.comp size.bound + 1
    correct oracle ho a := by
      have hd := w.outputs (g a)
      rw [h a] at hd
      have hs : oracle (ea.encode a) = ed.encode (g a) := ho a
      rw [← hs] at hd
      have ht := outputs w.machine oracle (ea.encode a) (eb.encode (f a)) _ hd
      refine { steps := ht.steps, evals_in_steps := ht.evals_in_steps, steps_le_m := ?_ }
      apply ht.steps_le_m.trans
      rw [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_comp]
      rw [hs]
      exact Nat.add_le_add_right (natPolynomial_eval_mono w.time (size.length_le a)) 1 }
  targetOutput := size
  queryBound := Polynomial.X
  safeQuery oracle _ a t c hrun hq := by
    have hc := query_is_initial w.machine oracle (ea.encode a) t c hrun hq
    subst c
    refine ⟨a, ?_, ?_⟩ <;> simp [machine, OracleMachine.init]

end
end Paper2.Complexity.OracleDecode

namespace Paper2.SourceFaithful
open Computability Paper2.Complexity Paper2.ExactInput Paper2.Problem
open BinaryCompose FixedRootCodec
noncomputable section

/-- Genuine public-output transport, parameterized only by an executed decoder
and its correctness on all strict descriptions of the actual field value. -/
theorem public_hardness_of_decoder (w : Wiring) (L : Language)
    (decode : RootCode → FixedFieldOutput.Answer L)
    (program : Computes rootEncoding (FixedFieldOutput.answerEncoding L) decode)
    (correct : ∀ (c : RootCode) (x : L.coefficientField),
      c.MinimalRepresents (TractableAlgorithms.fieldEmbedding L x) →
      decode c = L.fieldPresentation.decode.symm x)
    (hard : FixedFieldOutput.SharpPHard w L) : Problem.SharpPHard w L := by
  refine ⟨⟨TractableAlgorithms.publicBoundedAnswers w L⟩, ?_⟩
  intro answers f hf
  obtain ⟨counting⟩ := hard f hf
  have he : ∀ G, decode (answers.answer G) = FixedFieldOutput.answer w L G := by
    intro G
    have hx : TractableAlgorithms.fieldEmbedding L
        (L.fieldPresentation.decode (FixedFieldOutput.answer w L G)) =
        (value w L G : ℂ) :=
      congrArg (fun z : Paper2.Tractable.AlgebraicComplex => (z : ℂ))
        (FixedFieldOutput.answer_correct w L G)
    have hc := answers.correct G
    rw [← hx] at hc
    simpa using correct (answers.answer G) _ hc
  exact ⟨counting.controlledCompose (OracleDecode.reduction program answers.outputBound he)⟩

/-- Unconditional strict public-output hardness. The varying-polynomial Sturm
counter, rank refinement, fixed-field recovery and exact validation are all
executed by the closed reverse codec, including arbitrary correct root codes. -/
theorem public_hardness_of_fixed_field (w : Wiring) (L : Language)
    (hard : FixedFieldOutput.SharpPHard w L) : Problem.SharpPHard w L := by
  exact public_hardness_of_decoder w L
    (reverseRootCoordinates L.fieldPresentation (TractableAlgorithms.fieldEmbedding L))
    (reverseRootCoordinatesComputes L.fieldPresentation (TractableAlgorithms.fieldEmbedding L))
    (fun c x hc => reverseRootCoordinates_correct L.fieldPresentation
      (TractableAlgorithms.fieldEmbedding L) c x hc) hard

end
end Paper2.SourceFaithful
