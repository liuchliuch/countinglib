import Paper2.Complexity.BellMachines.QueryPotential
import Paper2.Complexity.BellMachines.UniversalPairReduction.SmoothingCompiler.ThreeQueryReduction

/-! All queries on every actual run prefix are the three encoded valid queries
produced by the ordinary input compiler. This upgrades the real three-call
program to the project's length-controlled oracle-reduction notion. -/
namespace Paper2.Complexity.UniversalPairReduction.ThreeQuery
open Turing Computability BinaryCompose Paper2.Algebraic StackProtocol
open BellMachines.QueryPotential
variable (a b : BinaryCompose.Machine)

/-- Exhaustive control inspection, preserving the actual query-stack contents. -/
theorem query_remaining_cases (c : (machine a b).Cfg)
    (hq : (machine a b).IsQuery c) :
    queryCost (machine a b) c = 1 ∧
      (remaining a b c = 3 ∨ remaining a b c = 2 ∨ remaining a b c = 1) := by
  rcases c with ⟨l, state, tapes⟩
  rcases hq with ⟨label, next, hl, hp⟩
  cases hl
  cases label with
  | inl j => simp [machine, program] at hp
  | inr j =>
    cases j with
    | inl j => simp [machine, program] at hp
    | inr i =>
      fin_cases i <;>
        simp_all [machine, program, protocol, queryCost, remaining, remainingLabel]

/-- The three query configurations actually occur, with the three original
query words. Arbitrary oracle answers affect later times but not query words. -/
theorem query_prefixes (oracle : List Bool → List Bool)
    (input x y z context : List Bool) (n : ℕ)
    (ha : (fun p => p.bind a.computer.step)^[n]
      (some (initList a.computer input)) =
      some (haltList a.computer (word x y z context))) :
    (∃ t, (machine a b).run oracle input t =
      some (stageCfg a b 2 (frame y ++ (frame z ++ context)) x [] [] [])) ∧
    (∃ t, (machine a b).run oracle input t =
      some (stageCfg a b 6 (frame z ++ context) y [] (oracle x).reverse [])) ∧
    (∃ t, (machine a b).run oracle input t =
      some (stageCfg a b 10 context z [] (oracle x).reverse (oracle y).reverse)) := by
  have first := OracleOneQuery.ordinary_run (M := machine a b)
    (leftLayout a b) (leftStates a b) (firstLabel a b) (some (admin a b 0))
    (fun _ => rfl) oracle _ _ n ha
  change RunsExactly ((machine a b).step oracle)
    (leftCfg a b (initList a.computer input))
    (leftCfg a b (haltList a.computer (word x y z context))) n at first
  rw [left_init, left_halt] at first
  have e1 := extract_run a b oracle 0 1 2 rfl rfl x
    (frame y ++ (frame z ++ context)) [] []
  have q1 := query_run a b oracle 2 3 rfl (frame y ++ (frame z ++ context)) x [] []
  have s1 := save_one_run a b oracle (frame y ++ (frame z ++ context)) (oracle x) []
  have e2 := extract_run a b oracle 4 5 6 rfl rfl y (frame z ++ context) (oracle x).reverse []
  have q2 := query_run a b oracle 6 7 rfl (frame z ++ context) y (oracle x).reverse []
  have s2 := save_two_run a b oracle (frame z ++ context) (oracle y) (oracle x).reverse
  have e3 := extract_run a b oracle 8 9 10 rfl rfl z context
    (oracle x).reverse (oracle y).reverse
  have p1 := first.trans e1
  have p2 := ((p1.trans q1).trans s1).trans e2
  have p3 := ((p2.trans q2).trans s2).trans e3
  exact ⟨⟨_, p1⟩, ⟨_, p2⟩, ⟨_, p3⟩⟩

/-- A query's positive potential identifies one of the already exhibited calls.
The strict potential lemma rules out any extra query at an intermediate time. -/
theorem every_query_word (oracle : List Bool → List Bool)
    (input x y z context : List Bool) (n : ℕ)
    (ha : (fun p => p.bind a.computer.step)^[n]
      (some (initList a.computer input)) =
      some (haltList a.computer (word x y z context)))
    (t : ℕ) (c : (machine a b).Cfg)
    (hc : (machine a b).run oracle input t = some c)
    (hq : (machine a b).IsQuery c) :
    c.stk (machine a b).queryStack = x ∨
      c.stk (machine a b).queryStack = y ∨
      c.stk (machine a b).queryStack = z := by
  obtain ⟨⟨t1, h1⟩, ⟨t2, h2⟩, ⟨t3, h3⟩⟩ := query_prefixes a b oracle input x y z context n ha
  obtain ⟨hcost, hrem | hrem | hrem⟩ := query_remaining_cases a b c hq
  · have ht := unique_query_time ((machine a b).step oracle) (queryCost (machine a b))
      (remaining a b) (potential a b oracle) ((machine a b).init input) c
      (stageCfg a b 2 (frame y ++ (frame z ++ context)) x [] [] []) t t1 hc h1 hcost
      (by simp [queryCost, stageCfg, cfg, machine, program, protocol, admin])
      (by simpa [remaining, remainingLabel, stageCfg, cfg, admin] using hrem)
    have he := Option.some.inj (hc.symm.trans (ht ▸ h1))
    subst c
    exact Or.inl (by simp [machine, stageCfg, cfg])
  · have ht := unique_query_time ((machine a b).step oracle) (queryCost (machine a b))
      (remaining a b) (potential a b oracle) ((machine a b).init input) c
      (stageCfg a b 6 (frame z ++ context) y [] (oracle x).reverse []) t t2 hc h2 hcost
      (by simp [queryCost, stageCfg, cfg, machine, program, protocol, admin])
      (by simpa [remaining, remainingLabel, stageCfg, cfg, admin] using hrem)
    have he := Option.some.inj (hc.symm.trans (ht ▸ h2))
    subst c
    exact Or.inr (Or.inl (by simp [machine, stageCfg, cfg]))
  · have ht := unique_query_time ((machine a b).step oracle) (queryCost (machine a b))
      (remaining a b) (potential a b oracle) ((machine a b).init input) c
      (stageCfg a b 10 context z [] (oracle x).reverse (oracle y).reverse) t t3 hc h3 hcost
      (by simp [queryCost, stageCfg, cfg, machine, program, protocol, admin])
      (by simpa [remaining, remainingLabel, stageCfg, cfg, admin] using hrem)
    have he := Option.some.inj (hc.symm.trans (ht ▸ h3))
    subst c
    exact Or.inr (Or.inr (by simp [machine, stageCfg, cfg]))

variable {α β γ δ ε : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {eq : Encoding γ Bool} {ed : Encoding δ Bool} {ee : Encoding ε Bool}
  {pre : α → γ × (γ × (γ × ε))} {post : δ × (δ × (δ × ε)) → β} {g : γ → δ}

/-- The original source reduction plus proved actual-run validity and polynomial
query lengths. The target answer-size witness controls all three actual answers. -/
noncomputable def controlledReduction
    (A : Computes ea (contextEncoding eq ee) pre)
    (B : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g) :
    LengthControlledOracleReduction ea eb eq ed (fun x => post (answers g (pre x))) g where
  reduction := reduction A B size
  targetOutput := size
  queryBound := A.outputBound.bound
  safeQuery oracle _ x t c hc hq := by
    have hw := every_query_word A.machine B.machine oracle (ea.encode x)
      (eq.encode (pre x).1) (eq.encode (pre x).2.1) (eq.encode (pre x).2.2.1)
      (ee.encode (pre x).2.2.2) (A.outputs x).steps (A.outputs x).evals_in_steps t c hc hq
    have hb := query_context_length_le A x
    rcases hw with hw | hw | hw
    · exact ⟨(pre x).1, hw, hw ▸ hb.1⟩
    · exact ⟨(pre x).2.1, hw, hw ▸ hb.2.1⟩
    · exact ⟨(pre x).2.2.1, hw, hw ▸ hb.2.2.1⟩

/-- Same finite machine and same polynomial as the already checked three-call
compiler: adding query safety does not change the execution. -/
@[simp] theorem controlledReduction_same_machine
    (A : Computes ea (contextEncoding eq ee) pre)
    (B : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g) :
    (controlledReduction A B size).reduction.machine = (reduction A B size).machine := rfl

/-- Exact mathematical postprocessing identities change only the specification;
the finite program, polynomial cost, and every query remain the same. -/
noncomputable def controlledOfEq
    (A : Computes ea (contextEncoding eq ee) pre)
    (B : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g)
    (f : α → β) (heq : ∀ x, f x = post (answers g (pre x))) :
    LengthControlledOracleReduction ea eb eq ed f g where
  reduction := of_eq A B size f heq
  targetOutput := size
  queryBound := A.outputBound.bound
  safeQuery := (controlledReduction A B size).safeQuery

theorem controlledOfEq_atMostThree
    (A : Computes ea (contextEncoding eq ee) pre)
    (B : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g)
    (f : α → β) (heq : ∀ x, f x = post (answers g (pre x))) :
    AtMostQueries (controlledOfEq A B size f heq).reduction.machine 3 :=
  of_eq_atMostThree A B size f heq

end Paper2.Complexity.UniversalPairReduction.ThreeQuery
