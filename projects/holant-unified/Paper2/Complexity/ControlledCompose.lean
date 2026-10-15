import Paper2.Complexity.OracleReductionCompose

/-! Query-safe execution traces for actual compiled oracle composition.
The existing compiler already proves polynomial transition time. This module
additionally tracks every external query through the actual copied callee run. -/
set_option backward.isDefEq.respectTransparency false

namespace Paper2.Complexity

namespace SafeTrace
variable {A : Type*}

/-- An actual finite run with a safety invariant at every pre-endpoint state. -/
structure Trace (step : A → Option A) (P : A → Prop) (a b : A) where
  steps : ℕ
  run : (fun c => c.bind step)^[steps] (some a) = some b
  safe : ∀ t, t < steps → ∀ c,
    (fun c => c.bind step)^[t] (some a) = some c → P c

def refl (step : A → Option A) (P : A → Prop) (a : A) : Trace step P a a :=
  ⟨0, rfl, by intro t ht; omega⟩

def one {step : A → Option A} {P : A → Prop} {a b : A}
    (h : step a = some b) (hp : P a) : Trace step P a b := by
  refine ⟨1, h, ?_⟩
  intro t ht c hc
  have ht0 : t = 0 := by omega
  subst t
  have he : a = c := Option.some.inj hc
  simpa only [← he] using hp

def Trace.trans {step : A → Option A} {P : A → Prop} {a b c : A}
    (h : Trace step P a b) (h' : Trace step P b c) : Trace step P a c := by
  refine ⟨h'.steps + h.steps, ?_, ?_⟩
  · rw [Function.iterate_add_apply, h.run, h'.run]
  · intro t ht d hd
    by_cases he : t < h.steps
    · exact h.safe t he d hd
    · have he : h.steps ≤ t := by omega
      have eq : t = (t - h.steps) + h.steps := by omega
      rw [eq, Function.iterate_add_apply, h.run] at hd
      exact h'.safe (t - h.steps) (by omega) d hd

/-- A successful finite run has a successful state at every earlier prefix. -/
theorem prefix_exists {step : A → Option A} {a b : A} {n t : ℕ}
    (h : (fun c => c.bind step)^[n] (some a) = some b) (ht : t ≤ n) :
    ∃ c, (fun c => c.bind step)^[t] (some a) = some c := by
  cases hp : (fun c => c.bind step)^[t] (some a) with
  | some c => exact ⟨c, rfl⟩
  | none =>
    have eq : n = (n - t) + t := by omega
    rw [eq, Function.iterate_add_apply, hp] at h
    have hn : ∀ k, (fun c : Option A => c.bind step)^[k] none = none := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl
    rw [hn] at h
    contradiction

/-- Safety extends to every reachable state when the endpoint is safe and halted. -/
theorem all_prefixes {step : A → Option A} {P : A → Prop} {a b : A}
    (h : Trace step P a b) (hb : P b) (halt : step b = none)
    (t : ℕ) (c : A) (hc : (fun c => c.bind step)^[t] (some a) = some c) : P c := by
  by_cases ht : t < h.steps
  · exact h.safe t ht c hc
  · have eq : t = (t - h.steps) + h.steps := by omega
    rw [eq, Function.iterate_add_apply, h.run] at hc
    cases hd : t - h.steps with
    | zero => simpa [hd] using (show P c from by
        have he : b = c := Option.some.inj (by simpa [hd] using hc)
        simpa only [← he] using hb)
    | succ n =>
      rw [hd, Function.iterate_succ_apply, Option.bind_some, halt] at hc
      have hn : ∀ k, (fun c : Option A => c.bind step)^[k] none = none := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl
      rw [hn] at hc
      contradiction


structure Witness {B : Type*} (step : B → Option B) (P : B → Prop)
    (R : A → B → Prop) (start : B) (source : A) where
  target : B
  related : R source target
  trace : Trace step P start target

def liftPrefix {B : Type*} (f : A → Option A) (g : B → Option B)
    (P : B → Prop) (R : A → B → Prop)
    (a₀ : A) (b₀ : B) (initial : R a₀ b₀) (n : ℕ)
    (simulate : ∀ t, t < n → ∀ a a' b,
      (fun p => p.bind f)^[t] (some a₀) = some a →
      f a = some a' → R a b → Witness g P R b a')
    (a : A) (run : (fun p => p.bind f)^[n] (some a₀) = some a) :
    Witness g P R b₀ a := by
  induction n generalizing a with
  | zero =>
    have ha : a₀ = a := Option.some.inj run
    subst a
    exact ⟨b₀, initial, refl g P b₀⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at run
    cases hp : (fun p => p.bind f)^[n] (some a₀) with
    | none => simp [hp] at run
    | some previous =>
      have hs : f previous = some a := by simpa [hp] using run
      let earlier := ih (fun t ht => simulate t (Nat.lt_trans ht (Nat.lt_succ_self n))) previous hp
      let next := simulate n (Nat.lt_succ_self n) previous a earlier.target hp hs earlier.related
      exact ⟨next.target, next.related, earlier.trace.trans next.trace⟩

end SafeTrace

namespace SafeStackProtocol
open Turing StackProtocol SafeTrace
variable {K Λ τ : Type} [DecidableEq K]
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (P : Cfg K Λ τ → Prop)

def clear_update (stack : K) (loop next : Λ)
    (h : ExecutesAt step loop (clearStmt stack loop next))
    (safeLoop : ∀ state tapes, P ⟨some loop, state, tapes⟩)
    (memory : τ) (tapes : K → List Bool) (word : List Bool) :
    Trace step P (cfg loop memory (Function.update tapes stack word))
      (cfg next memory (Function.update tapes stack [])) := by
  induction word with
  | nil => exact one (clear_step_nil step stack loop next h memory tapes) (safeLoop _ _)
  | cons bit word ih =>
    exact (one (clear_step_cons step stack loop next h memory tapes bit word) (safeLoop _ _)).trans ih

def clear (stack : K) (loop next : Λ)
    (h : ExecutesAt step loop (clearStmt stack loop next))
    (safeLoop : ∀ state tapes, P ⟨some loop, state, tapes⟩)
    (memory : τ) (tapes : K → List Bool) :
    Trace step P (cfg loop memory tapes) (cfg next memory (Function.update tapes stack [])) := by
  simpa using clear_update step P stack loop next h safeLoop memory tapes (tapes stack)

variable (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)

def copy_move (loop next : Λ) (h : ExecutesAt step loop (copyMoveStmt src tmp loop next))
    (safeLoop : ∀ state tapes, P ⟨some loop, state, tapes⟩)
    (memory : τ) (frame : K → List Bool) (source destination temporary : List Bool) :
    Trace step P (cfg loop memory (tapes3 frame src dst tmp source destination temporary))
      (cfg next memory (tapes3 frame src dst tmp [] destination (source.reverse ++ temporary))) := by
  induction source generalizing temporary with
  | nil => exact one (copy_move_step_nil src dst tmp hsd hst step loop next h
      memory frame destination temporary) (safeLoop _ _)
  | cons bit source ih =>
    have run := (one (copy_move_step_cons src dst tmp hsd hst step loop next h
      memory frame bit source destination temporary) (safeLoop _ _)).trans (ih (bit :: temporary))
    simpa [List.reverse_cons, List.append_assoc] using run

def copy_restore (loop next : Λ)
    (h : ExecutesAt step loop (copyRestoreStmt src dst tmp loop next))
    (safeLoop : ∀ state tapes, P ⟨some loop, state, tapes⟩)
    (memory : τ) (frame : K → List Bool) (temporary source destination : List Bool) :
    Trace step P (cfg loop memory (tapes3 frame src dst tmp source destination temporary))
      (cfg next memory (tapes3 frame src dst tmp (temporary.reverse ++ source)
        (temporary.reverse ++ destination) [])) := by
  induction temporary generalizing source destination with
  | nil => exact one (copy_restore_step_nil src dst tmp step loop next h
      memory frame source destination) (safeLoop _ _)
  | cons bit temporary ih =>
    have run := (one (copy_restore_step_cons src dst tmp hsd hst hdt step loop next h
      memory frame bit source destination temporary) (safeLoop _ _)).trans
      (ih (bit :: source) (bit :: destination))
    simpa [List.reverse_cons, List.append_assoc] using run

def copy_frame (move restore next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyRestoreStmt src dst tmp restore next))
    (safeMove : ∀ state tapes, P ⟨some move, state, tapes⟩)
    (safeRestore : ∀ state tapes, P ⟨some restore, state, tapes⟩)
    (memory : τ) (frame : K → List Bool) (source destination : List Bool) :
    Trace step P (cfg move memory (tapes3 frame src dst tmp source destination []))
      (cfg next memory (tapes3 frame src dst tmp source (source ++ destination) [])) := by
  have moveRun := copy_move step P src dst tmp hsd hst move restore hm safeMove
    memory frame source destination []
  simp only [List.append_nil] at moveRun
  have run := moveRun.trans (copy_restore step P src dst tmp hsd hst hdt restore next hr
    safeRestore memory frame source.reverse [] destination)
  simpa using run

def copy (move restore next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyRestoreStmt src dst tmp restore next))
    (safeMove : ∀ state tapes, P ⟨some move, state, tapes⟩)
    (safeRestore : ∀ state tapes, P ⟨some restore, state, tapes⟩)
    (memory : τ) (tapes : K → List Bool) (htmp : tapes tmp = []) :
    Trace step P (cfg move memory tapes)
      (cfg next memory (Function.update tapes dst (tapes src ++ tapes dst))) := by
  have hbefore : tapes3 tapes src dst tmp (tapes src) (tapes dst) [] = tapes := by
    simp [tapes3, ← htmp]
  have hafter : tapes3 tapes src dst tmp (tapes src) (tapes src ++ tapes dst) [] =
      Function.update tapes dst (tapes src ++ tapes dst) := by
    funext k
    by_cases ht : k = tmp
    · subst k; simp [tapes3, Ne.symm hdt, htmp]
    · simp [tapes3, Function.update_apply, ht]
  simpa only [hbefore, hafter] using copy_frame step P src dst tmp hsd hst hdt
    move restore next hm hr safeMove safeRestore memory tapes (tapes src) (tapes dst)

end SafeStackProtocol

namespace OracleInline
open Turing StackProtocol SafeTrace
variable {J R τ : Type} [DecidableEq J] [Fintype J] [Fintype R] [Fintype τ]

/-- Every intermediate prepare state is safe, not merely its final state. -/
def prepare_safe (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool)
    (P : (machine m query answer initialMemory ret outside).Cfg → Prop)
    (safeProtocol : ∀ p state tapes, P ⟨some (phase m R p), state, tapes⟩)
    (memory : τ) (frame : J → List Bool) :
    Trace ((machine m query answer initialMemory ret outside).step oracle) P
      (cfg m (phase m R 0) memory (fun _ => []) frame)
      (calleeCfg m (m.init (frame query)) memory frame) := by
  let step := (machine m query answer initialMemory ret outside).step oracle
  have hp := executes_protocol m query answer initialMemory ret outside oracle
  have hm : ExecutesAt step (phase m R 0)
      (copyMoveStmt (callerTape m query) (temporary m J) (phase m R 0) (phase m R 1)) := by
    simpa [protocol, step] using hp 0
  have hr : ExecutesAt step (phase m R 1)
      (copyRestoreStmt (callerTape m query) (.inl m.inputStack) (temporary m J)
        (phase m R 1) (phase m R 2)) := by
    simpa [protocol, step] using hp 1
  have hc := SafeStackProtocol.copy step P (callerTape m query) (.inl m.inputStack) (temporary m J)
    (by simp [callerTape]) (by simp [callerTape, temporary]) (by simp [temporary])
    (phase m R 0) (phase m R 1) (phase m R 2) hm hr
    (safeProtocol 0) (safeProtocol 1)
    (m.initialState, memory) (tapes m (fun _ => []) frame) rfl
  have hi : Function.update (fun _ : m.K => ([] : List Bool)) m.inputStack (frame query) =
      (m.init (frame query)).stk := by
    funext k; simp [OracleMachine.init, Function.update]
  have hc' : Trace step P
      (cfg m (phase m R 0) memory (fun _ => []) frame)
      (cfg m (phase m R 2) memory (m.init (frame query)).stk frame) := by
    change Trace step P
      (StackProtocol.cfg (phase m R 0) (m.initialState, memory) (tapes m (fun _ => []) frame))
      (StackProtocol.cfg (phase m R 2) (m.initialState, memory)
        (tapes m (m.init (frame query)).stk frame))
    change Trace step P _
      (StackProtocol.cfg (phase m R 2) (m.initialState, memory)
        (Function.update (tapes m (fun _ => []) frame) (.inl m.inputStack)
          (frame query ++ []))) at hc
    simpa only [List.append_nil, update_callee, hi] using hc
  have he : step (cfg m (phase m R 2) memory (m.init (frame query)).stk frame) =
      some (calleeCfg m (m.init (frame query)) memory frame) := by
    change step (StackProtocol.cfg (phase m R 2) (m.initialState, memory)
      (tapes m (m.init (frame query)).stk frame)) = _
    calc
      _ = some (TM2.stepAux (protocol m query answer ret 2) (none, (m.initialState, memory))
          (tapes m (m.init (frame query)).stk frame)) := hp 2 _ _
      _ = _ := by simp [protocol, TM2.stepAux, calleeCfg, OracleMachine.init, tapes]
  exact hc'.trans (one he (safeProtocol 2 _ _))

/-- Copy-back and cleanup perform no unchecked external query. -/
def finish_safe (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool)
    (P : (machine m query answer initialMemory ret outside).Cfg → Prop)
    (safeProtocol : ∀ p state tapes, P ⟨some (phase m R p), state, tapes⟩)
    (memory : τ) (frame : J → List Bool) (value : List Bool) :
    Trace ((machine m query answer initialMemory ret outside).step oracle) P
      (calleeCfg m (m.output value) memory frame)
      (cfg m (.inr (.inr (ret memory))) memory (fun _ => []) (Function.update frame answer value)) := by
  let step := (machine m query answer initialMemory ret outside).step oracle
  have hp := executes_protocol m query answer initialMemory ret outside oracle
  let outputTapes := (m.output value).stk
  have hc := SafeStackProtocol.clear step P (callerTape m answer) (phase m R 3) (phase m R 4)
    (by simpa [protocol, step] using hp 3) (safeProtocol 3)
    (m.initialState, memory) (tapes m outputTapes frame)
  have hc' : Trace step P (calleeCfg m (m.output value) memory frame)
      (cfg m (phase m R 4) memory outputTapes (Function.update frame answer [])) := by
    change Trace step P _
      (StackProtocol.cfg (phase m R 4) (m.initialState, memory)
        (Function.update (tapes m outputTapes frame) (callerTape m answer) [])) at hc
    rw [update_caller] at hc
    exact hc
  have hcopy := SafeStackProtocol.copy step P (.inl m.outputStack) (callerTape m answer) (temporary m J)
    (by simp [callerTape]) (by simp [temporary]) (by simp [callerTape, temporary])
    (phase m R 4) (phase m R 5) (phase m R 6)
    (by simpa [protocol, step] using hp 4) (by simpa [protocol, step] using hp 5)
    (safeProtocol 4) (safeProtocol 5)
    (m.initialState, memory) (tapes m outputTapes (Function.update frame answer [])) rfl
  have ho : tapes m outputTapes (Function.update frame answer []) (.inl m.outputStack) = value := by
    simp only [tapes, Sum.elim_inl, outputTapes, OracleMachine.output, ite_true]
  have ha : tapes m outputTapes (Function.update frame answer []) (callerTape m answer) = [] := by
    simp only [tapes, callerTape, Sum.elim_inr, Sum.elim_inl, Function.update_self]
  rw [ho, ha, List.append_nil, update_caller, Function.update_idem] at hcopy
  have hcopy' : Trace step P
      (cfg m (phase m R 4) memory outputTapes (Function.update frame answer []))
      (cfg m (phase m R 6) memory outputTapes (Function.update frame answer value)) := hcopy
  have hclean := SafeStackProtocol.clear step P (.inl m.outputStack) (phase m R 6) (phase m R 7)
    (by simpa [protocol, step] using hp 6) (safeProtocol 6) (m.initialState, memory)
    (tapes m outputTapes (Function.update frame answer value))
  have ho' : tapes m outputTapes (Function.update frame answer value) (.inl m.outputStack) = value := by
    simp only [tapes, Sum.elim_inl, outputTapes, OracleMachine.output, ite_true]
  have he : Function.update outputTapes m.outputStack [] = (fun _ => []) := by
    funext k
    by_cases h : k = m.outputStack <;> simp [outputTapes, OracleMachine.output, Function.update, h]
  rw [update_callee, he] at hclean
  have hclean' : Trace step P
      (cfg m (phase m R 6) memory outputTapes (Function.update frame answer value))
      (cfg m (phase m R 7) memory (fun _ => []) (Function.update frame answer value)) := hclean
  have hreturn : step (cfg m (phase m R 7) memory (fun _ => []) (Function.update frame answer value)) =
      some (cfg m (.inr (.inr (ret memory))) memory (fun _ => []) (Function.update frame answer value)) := by
    calc
      _ = some (TM2.stepAux (protocol m query answer ret 7) (none, (m.initialState, memory))
          (tapes m (fun _ => []) (Function.update frame answer value))) := hp 7 _ _
      _ = _ := by simp [protocol, TM2.stepAux, cfg]
  exact ((hc'.trans hcopy').trans hclean').trans (one hreturn (safeProtocol 7 _ _))


/-- Every source prefix is reproduced with identical tapes inside the callee. -/
theorem callee_run (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (c d : m.Cfg) (t : ℕ)
    (memory : τ) (frame : J → List Bool)
    (h : (fun p => p.bind (m.step oracle))^[t] (some c) = some d) :
    (fun p => p.bind ((machine m query answer initialMemory ret outside).step oracle))^[t]
      (some (calleeCfg m c memory frame)) = some (calleeCfg m d memory frame) := by
  have sourceRun := OracleSubroutine.run_program m (none, initialMemory)
    (fun _ : Option Bool × τ => (Sum.inl (3 : Fin 8) : Fin 8 ⊕ R))
    (fun l => OracleStateRename.command (stateEquiv m τ).symm
      (match l with
       | .inl p => .ordinary (protocol m query answer ret p)
       | .inr r => outside r))
    oracle c (none, memory) (Sum.elim frame (fun _ : Unit => [])) t d h
  have result := OracleStateRename.run (rawMachine m query answer initialMemory ret outside)
    (stateEquiv m τ) oracle
    (MachineReturn.cfg (fun _ : Option Bool × τ => (Sum.inl (3 : Fin 8) : Fin 8 ⊕ R))
      c (none, memory) (Sum.elim frame (fun _ : Unit => []))) t
  have result' := result.trans (congrArg
    (Option.map (OracleStateRename.cfg (rawMachine m query answer initialMemory ret outside)
      (stateEquiv m τ))) sourceRun)
  have hs : (machine m query answer initialMemory ret outside).step oracle =
      (OracleStateRename.machine (rawMachine m query answer initialMemory ret outside) (stateEquiv m τ)).step oracle := by
    funext q
    rcases q with ⟨label, state, data⟩
    cases label with
    | none => rfl
    | some label =>
      simp only [OracleMachine.step, machine]
      cases hc : (OracleStateRename.machine (rawMachine m query answer initialMemory ret outside)
        (stateEquiv m τ)).program label <;> simp_all only
  rw [hs]
  simpa only [OracleStateRename.cfg, MachineReturn.cfg, calleeCfg, stateEquiv, phase,
    Equiv.coe_fn_mk, Option.map_some] using result'

theorem protocol_not_query (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (p : Fin 8) (state : State m τ) (tapes : Tape m J → List Bool) :
    ¬ (machine m query answer initialMemory ret outside).IsQuery ⟨some (phase m R p), state, tapes⟩ := by
  rintro ⟨label, next, he, hq⟩
  have he' : phase m R p = label := Option.some.inj he
  subst label
  simp [machine, rawMachine, OracleStateRename.machine, OracleSubroutine.machine,
    OracleStateRename.command, phase] at hq

theorem callee_query_iff (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (c : m.Cfg) (memory : τ) (frame : J → List Bool) :
    (machine m query answer initialMemory ret outside).IsQuery (calleeCfg m c memory frame) ↔
      m.IsQuery c := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none =>
    simp only [OracleMachine.IsQuery, calleeCfg, Option.elim_none]
    simp [machine, rawMachine, OracleStateRename.machine, OracleSubroutine.machine,
      OracleStateRename.command, phase]
  | some label =>
    cases hp : m.program label with
    | ordinary q =>
      simp [OracleMachine.IsQuery, calleeCfg, machine, rawMachine, OracleStateRename.machine,
        OracleSubroutine.machine, OracleStateRename.command, hp]
    | query next =>
      simp [OracleMachine.IsQuery, calleeCfg, machine, rawMachine, OracleStateRename.machine,
        OracleSubroutine.machine, OracleStateRename.command, hp]

/-- Safety transfers pointwise through every real callee prefix. -/
def callee_safe (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (input output : List Bool) (time : ℕ)
    (P : (machine m query answer initialMemory ret outside).Cfg → Prop)
    (memory : τ) (frame : J → List Bool)
    (h : m.OutputsInTime oracle input output time)
    (safe : ∀ t c, m.run oracle input t = some c → P (calleeCfg m c memory frame)) :
    Trace ((machine m query answer initialMemory ret outside).step oracle) P
      (calleeCfg m (m.init input) memory frame) (calleeCfg m (m.output output) memory frame) := by
  refine ⟨h.steps, callee_run m query answer initialMemory ret outside oracle _ _ _ memory frame
    h.evals_in_steps, ?_⟩
  intro t ht c hc
  obtain ⟨source, hs⟩ := SafeTrace.prefix_exists h.evals_in_steps (Nat.le_of_lt ht)
  have he := callee_run m query answer initialMemory ret outside oracle _ _ t memory frame hs
  have hc' : calleeCfg m source memory frame = c := Option.some.inj (he.symm.trans hc)
  simpa only [← hc'] using safe t source hs

end OracleInline


namespace OracleCompose
open Turing SafeTrace

theorem cfg_not_query (callee caller : OracleMachine) (c : caller.Cfg) (saved : caller.Λ) :
    ¬ (machine callee caller).IsQuery (cfg callee caller c saved) := by
  rcases c with ⟨label, state, frame⟩
  cases label with
  | none => simp [OracleMachine.IsQuery, cfg]
  | some label =>
    rintro ⟨l, next, he, hq⟩
    have hl : Sum.inr (Sum.inr label) = l := Option.some.inj he
    subst l
    change (base callee caller).program (.inr (.inr label)) = .query next at hq
    rw [OracleInline.program_outside] at hq
    cases hp : caller.program label <;> simp [outside, hp] at hq

end OracleCompose

namespace LengthControlledOracleReduction
open Computability Turing SafeTrace
variable {α β γ δ ε ζ : Type}
variable {ea : Encoding α Bool} {eb : Encoding β Bool} {ec : Encoding γ Bool}
variable {ed : Encoding δ Bool} {ee : Encoding ε Bool} {ef : Encoding ζ Bool}
variable {f : α → β} {g : γ → δ} {h : ε → ζ}

/-- The composed query polynomial is the actual callee query bound applied to
its actual caller-query length bound. -/
def composedQuerySafe
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h) (a : α)
    (c : (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).Cfg) : Prop :=
  (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).IsQuery c →
    ∃ q, c.stk (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).queryStack = ee.encode q ∧
      (c.stk (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).queryStack).length ≤
        (r₂.queryBound.comp r₁.queryBound).eval (ea.encode a).length

/-- Each compiled caller step preserves query validity and query-length control,
including every state inside the finite copy/call/clear protocol. -/
noncomputable def safe_simulate_step
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (outer inner : List Bool → List Bool)
    (ho : RepresentsOracle ec ed g outer) (hi : RepresentsOracle ee ef h inner)
    (a : α) (t : ℕ) (c c' : r₁.reduction.machine.Cfg)
    (hr : r₁.reduction.machine.run outer (ea.encode a) t = some c)
    (hs : r₁.reduction.machine.step outer c = some c')
    (d : (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).Cfg)
    (hd : OracleCompose.Related r₂.reduction.machine r₁.reduction.machine c d) :
    SafeTrace.Witness
      ((OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).step inner)
      (composedQuerySafe r₁ r₂ a)
      (OracleCompose.Related r₂.reduction.machine r₁.reduction.machine) d c' := by
  classical
  apply Classical.choice
  obtain ⟨saved, rfl⟩ := hd
  rcases c with ⟨label, state, frame⟩
  cases label with
  | none => simp [OracleMachine.step] at hs
  | some label =>
    have outsideSafe : composedQuerySafe r₁ r₂ a
        (OracleCompose.cfg r₂.reduction.machine r₁.reduction.machine ⟨some label, state, frame⟩ saved) := by
      intro hq
      exact False.elim (OracleCompose.cfg_not_query _ _ _ _ hq)
    cases hp : r₁.reduction.machine.program label with
    | ordinary stmt =>
      have he : TM2.stepAux stmt state frame = c' := by
        simpa only [OracleMachine.step, hp, Option.some.injEq] using hs
      subst c'
      refine ⟨⟨_, ⟨saved, rfl⟩, ?_⟩⟩
      exact one (OracleCompose.ordinary_step _ _ inner label state frame saved stmt hp) outsideSafe
    | query next =>
      have he : (⟨some (next state), state,
          Function.update frame r₁.reduction.machine.answerStack
            (outer (frame r₁.reduction.machine.queryStack))⟩ : r₁.reduction.machine.Cfg) = c' := by
        simpa only [OracleMachine.step, hp, Option.some.injEq] using hs
      subst c'
      have hq : r₁.reduction.machine.IsQuery ⟨some label, state, frame⟩ := ⟨label, next, rfl, hp⟩
      obtain ⟨query, hquery, hlen⟩ := r₁.safeQuery outer ho a t _ hr hq
      change frame r₁.reduction.machine.queryStack = ec.encode query at hquery
      change (frame r₁.reduction.machine.queryStack).length ≤ _ at hlen
      let memory := (state, next state)
      have safeProtocol : ∀ p st tapes, composedQuerySafe r₁ r₂ a
          ⟨some (OracleInline.phase r₂.reduction.machine r₁.reduction.machine.Λ p), st, tapes⟩ := by
        intro p st tapes hbad
        exact False.elim (OracleInline.protocol_not_query r₂.reduction.machine
          r₁.reduction.machine.queryStack r₁.reduction.machine.answerStack
          (r₁.reduction.machine.initialState, r₁.reduction.machine.main) Prod.snd
          (OracleCompose.outside r₂.reduction.machine r₁.reduction.machine) p st tapes hbad)
      have hc : r₂.reduction.machine.OutputsInTime inner
          (frame r₁.reduction.machine.queryStack) (outer (frame r₁.reduction.machine.queryStack))
          (r₂.reduction.time.eval (frame r₁.reduction.machine.queryStack).length) := by
        change frame r₁.reduction.machine.queryStack = ec.encode query at hquery
        rw [hquery, ho]
        exact r₂.reduction.correct inner hi query
      have innerSafe : ∀ t' c₂,
          r₂.reduction.machine.run inner (frame r₁.reduction.machine.queryStack) t' = some c₂ →
          composedQuerySafe r₁ r₂ a (OracleInline.calleeCfg r₂.reduction.machine c₂ memory frame) := by
        intro t' c₂ hrun hbad
        have hbad' : r₂.reduction.machine.IsQuery c₂ :=
          (OracleInline.callee_query_iff r₂.reduction.machine
            r₁.reduction.machine.queryStack r₁.reduction.machine.answerStack
            (r₁.reduction.machine.initialState, r₁.reduction.machine.main) Prod.snd
            (OracleCompose.outside r₂.reduction.machine r₁.reduction.machine) c₂ memory frame).mp hbad
        obtain ⟨q₂, he₂, hl₂⟩ := r₂.safeQuery inner hi query t' c₂ (by simpa only [hquery] using hrun) hbad'
        refine ⟨q₂, he₂, ?_⟩
        change (c₂.stk r₂.reduction.machine.queryStack).length ≤ _
        rw [Polynomial.eval_comp]
        exact hl₂.trans (natPolynomial_eval_mono r₂.queryBound (by simpa only [hquery] using hlen))
      have prep := OracleInline.prepare_safe r₂.reduction.machine
        r₁.reduction.machine.queryStack r₁.reduction.machine.answerStack
        (r₁.reduction.machine.initialState, r₁.reduction.machine.main) Prod.snd
        (OracleCompose.outside r₂.reduction.machine r₁.reduction.machine) inner
        (composedQuerySafe r₁ r₂ a) safeProtocol memory frame
      have call := OracleInline.callee_safe r₂.reduction.machine
        r₁.reduction.machine.queryStack r₁.reduction.machine.answerStack
        (r₁.reduction.machine.initialState, r₁.reduction.machine.main) Prod.snd
        (OracleCompose.outside r₂.reduction.machine r₁.reduction.machine) inner _ _ _
        (composedQuerySafe r₁ r₂ a) memory frame hc innerSafe
      have finish := OracleInline.finish_safe r₂.reduction.machine
        r₁.reduction.machine.queryStack r₁.reduction.machine.answerStack
        (r₁.reduction.machine.initialState, r₁.reduction.machine.main) Prod.snd
        (OracleCompose.outside r₂.reduction.machine r₁.reduction.machine) inner
        (composedQuerySafe r₁ r₂ a) safeProtocol memory frame (outer (frame r₁.reduction.machine.queryStack))
      rw [← OracleCompose.step_machine] at prep call finish
      refine ⟨⟨_, ⟨next state, rfl⟩, ?_⟩⟩
      exact (one (OracleCompose.query_launch _ _ inner label state frame saved next hp) outsideSafe).trans
        ((prep.trans call).trans finish)


/-- Fully length-controlled transitivity of the concrete compiled machine.
Every external query is an actual valid final-target input with polynomial length. -/
noncomputable def controlledCompose
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h) :
    LengthControlledOracleReduction ea eb ee ef f h where
  reduction := r₁.compose r₂.reduction
  targetOutput := r₂.targetOutput
  queryBound := r₂.queryBound.comp r₁.queryBound
  safeQuery oracle ho a t c hr hq := by
    let outer := encodedOracle ec ed g
    have houter : RepresentsOracle ec ed g outer := encodedOracle_represents ec ed g
    have sourceRun := r₁.reduction.correct outer houter a
    let run := SafeTrace.liftPrefix (r₁.reduction.machine.step outer)
      ((OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).step oracle)
      (composedQuerySafe r₁ r₂ a)
      (OracleCompose.Related r₂.reduction.machine r₁.reduction.machine)
      (r₁.reduction.machine.init (ea.encode a))
      ((OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).init (ea.encode a))
      ⟨r₁.reduction.machine.main, (OracleCompose.cfg_init _ _ _).symm⟩ sourceRun.steps
      (fun t' _ source target compiled hs hstep related =>
        safe_simulate_step r₁ r₂ outer oracle houter ho a t' source target hs hstep compiled related)
      (r₁.reduction.machine.output (eb.encode (f a))) sourceRun.evals_in_steps
    have hend : run.target =
        (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).output (eb.encode (f a)) := by
      obtain ⟨saved, he⟩ := run.related
      rw [he, OracleCompose.cfg_output]
    have trace := run.trace
    rw [hend] at trace
    have outputSafe : composedQuerySafe r₁ r₂ a
        ((OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).output (eb.encode (f a))) := by
      intro hbad
      simp [OracleMachine.IsQuery, OracleMachine.output] at hbad
    exact (SafeTrace.all_prefixes trace outputSafe rfl t c hr) hq

end LengthControlledOracleReduction
end Paper2.Complexity
