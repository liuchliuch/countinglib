import Counting.Algorithm.KarpLubyRequest.Whole.ArrayObserver
import Holant.Complexity.GraphPreprocessing.Primitive

/-!
An array-backed observer of the original Boolean TM2 syntax. Each primitive
instruction is interpreted once, on the actual branch, and contributes exactly
one to the canonical primitive counter. No machine transition is skipped.
-/
namespace Counting.Algorithm.KarpLubyRequest.Whole.ArrayPrimitive

open Turing Holant.Complexity
open ArrayObserver

variable {K L S : Type} {n : ℕ} [DecidableEq K]

abbrev Statement := TM2.Stmt (fun _ : K => Bool) L S
abbrev Program := L → Statement (K := K) (L := L) (S := S)

/-- Execute the original syntax on the array bank, counting every primitive. -/
def exec (e : Fin n ≃ K) : Statement (K := K) (L := L) (S := S) →
    S → Bank n → ℕ × Config n L S
  | .push k f q, v, b =>
    let r := exec e q v (write e b k (f v :: read e b k))
    (r.1 + 1, r.2)
  | .pop k f q, v, b =>
    let word := read e b k
    let r := exec e q (f v word.head?) (write e b k word.tail)
    (r.1 + 1, r.2)
  | .peek k f q, v, b =>
    let r := exec e q (f v (read e b k).head?) b
    (r.1 + 1, r.2)
  | .load f q, v, b =>
    let r := exec e q (f v) b
    (r.1 + 1, r.2)
  | .branch f a b, v, bank =>
    let r := if f v then exec e a v bank else exec e b v bank
    (r.1 + 1, r.2)
  | .goto f, v, b => (1, ⟨some (f v), v, b⟩)
  | .halt, v, b => (1, ⟨none, v, b⟩)

/-- Both the charged cost and the complete represented endpoint are exact. -/
theorem exec_eq (e : Fin n ≃ K) (q : Statement (K := K) (L := L) (S := S))
    (v : S) (b : Bank n) :
    ((exec e q v b).1, toCfg e (exec e q v b).2) =
      TM2Cost.primitiveRun q v (read e b) := by
  induction q generalizing v b with
  | push k f q ih =>
    dsimp only [exec, TM2Cost.primitiveRun]
    rw [← read_write e b k (f v :: read e b k)]
    exact congrArg (fun r : ℕ × TM2.Cfg (fun _ : K => Bool) L S => (r.1 + 1, r.2))
      (ih v (write e b k (f v :: read e b k)))
  | pop k f q ih =>
    dsimp only [exec, TM2Cost.primitiveRun]
    rw [← read_write e b k (read e b k).tail]
    exact congrArg (fun r : ℕ × TM2.Cfg (fun _ : K => Bool) L S => (r.1 + 1, r.2))
      (ih (f v (read e b k).head?) (write e b k (read e b k).tail))
  | peek k f q ih =>
    dsimp only [exec, TM2Cost.primitiveRun]
    exact congrArg (fun r : ℕ × TM2.Cfg (fun _ : K => Bool) L S => (r.1 + 1, r.2))
      (ih (f v (read e b k).head?) b)
  | load f q ih =>
    dsimp only [exec, TM2Cost.primitiveRun]
    exact congrArg (fun r : ℕ × TM2.Cfg (fun _ : K => Bool) L S => (r.1 + 1, r.2))
      (ih (f v) b)
  | branch f qa qb ha hb =>
    cases hv : f v with
    | false =>
      dsimp only [exec, TM2Cost.primitiveRun]
      simp only [hv, Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun r : ℕ × TM2.Cfg (fun _ : K => Bool) L S => (r.1 + 1, r.2))
        (hb v b)
    | true =>
      dsimp only [exec, TM2Cost.primitiveRun]
      simp only [hv, ↓reduceIte]
      exact congrArg (fun r : ℕ × TM2.Cfg (fun _ : K => Bool) L S => (r.1 + 1, r.2))
        (ha v b)
  | goto f => rfl
  | halt => rfl

theorem exec_cost (e : Fin n ≃ K) (q : Statement (K := K) (L := L) (S := S))
    (v : S) (b : Bank n) :
    (exec e q v b).1 = (TM2Cost.primitiveRun q v (read e b)).1 :=
  congrArg Prod.fst (exec_eq e q v b)

theorem exec_result (e : Fin n ≃ K) (q : Statement (K := K) (L := L) (S := S))
    (v : S) (b : Bank n) :
    toCfg e (exec e q v b).2 = TM2.stepAux q v (read e b) :=
  (congrArg Prod.snd (exec_eq e q v b)).trans (TM2Cost.primitiveRun_result q v (read e b))

/-- One original transition, with the canonical treatment of halted inputs. -/
def tick (e : Fin n ≃ K) (program : Program (K := K) (L := L) (S := S)) :
    Option (Config n L S) → ℕ × Option (Config n L S)
  | none => (0, none)
  | some c => match c.l with
    | none => (0, none)
    | some label => let r := exec e (program label) c.var c.stk; (r.1, some r.2)

theorem tick_eq (e : Fin n ≃ K) (program : Program (K := K) (L := L) (S := S))
    (c : Option (Config n L S)) :
    ((tick e program c).1, (tick e program c).2.map (toCfg e)) =
      GraphPreprocessing.Primitive.tick program (c.map (toCfg e)) := by
  cases c with
  | none => rfl
  | some c =>
    cases c with
    | mk label state bank =>
      cases label with
      | none => rfl
      | some label =>
        exact congrArg (fun r : ℕ × TM2.Cfg (fun _ : K => Bool) L S => (r.1, some r.2))
          (exec_eq e (program label) state bank)

/-- Tail-recursive accumulation avoids building a host-language call chain. -/
def measure (e : Fin n ≃ K) (program : Program (K := K) (L := L) (S := S)) :
    ℕ → ℕ → Option (Config n L S) → ℕ × Option (Config n L S)
  | 0, cost, c => (cost, c)
  | fuel + 1, cost, c =>
    let first := tick e program c
    measure e program fuel (cost + first.1) first.2

/-- Exact accumulated cost and all physical stacks agree with the existing
primitive interpreter, for every fuel and every starting array configuration. -/
theorem measure_eq (e : Fin n ≃ K) (program : Program (K := K) (L := L) (S := S))
    (fuel cost : ℕ) (c : Option (Config n L S)) :
    ((measure e program fuel cost c).1, (measure e program fuel cost c).2.map (toCfg e)) =
      (cost + (GraphPreprocessing.Primitive.run program fuel (c.map (toCfg e))).1,
        (GraphPreprocessing.Primitive.run program fuel (c.map (toCfg e))).2) := by
  induction fuel generalizing cost c with
  | zero => rfl
  | succ fuel ih =>
    dsimp only [measure]
    rw [ih]
    have hcost := congrArg Prod.fst (tick_eq e program c)
    have hcfg := congrArg Prod.snd (tick_eq e program c)
    dsimp only at hcost hcfg
    rw [hcost, hcfg]
    dsimp only [GraphPreprocessing.Primitive.run]
    rw [Nat.add_assoc]

def run (e : Fin n ≃ K) (program : Program (K := K) (L := L) (S := S))
    (fuel : ℕ) (c : Option (Config n L S)) : ℕ × Option (Config n L S) :=
  measure e program fuel 0 c

theorem run_eq (e : Fin n ≃ K) (program : Program (K := K) (L := L) (S := S))
    (fuel : ℕ) (c : Option (Config n L S)) :
    ((run e program fuel c).1, (run e program fuel c).2.map (toCfg e)) =
      GraphPreprocessing.Primitive.run program fuel (c.map (toCfg e)) := by
  simpa only [run, Nat.zero_add] using measure_eq e program fuel 0 c

/-- A single tail-recursive pass records both transitions and primitive cost.
The original halted configuration is returned before attempting another tick. -/
def seek (e : Fin n ≃ K) (program : Program (K := K) (L := L) (S := S)) :
    ℕ → ℕ → ℕ → Config n L S → Option (ℕ × ℕ × Config n L S)
  | 0, used, cost, c => match c.l with
    | none => some (used, cost, c)
    | some _ => none
  | fuel + 1, used, cost, c => match c.l with
    | none => some (used, cost, c)
    | some label =>
      let first := exec e (program label) c.var c.stk
      seek e program fuel (used + 1) (cost + first.1) first.2

/-- A successful stopping observer is an exact prefix of the array interpreter.
The counters are accumulated values, and the returned endpoint is halted. -/
theorem seek_measure (e : Fin n ≃ K) (program : Program (K := K) (L := L) (S := S))
    (fuel used cost : ℕ) (c : Config n L S) (time paid : ℕ) (ending : Config n L S)
    (h : seek e program fuel used cost c = some (time, paid, ending)) :
    ∃ steps, steps ≤ fuel ∧ time = used + steps ∧
      measure e program steps cost (some c) = (paid, some ending) ∧ ending.l = none := by
  induction fuel generalizing used cost c with
  | zero =>
    cases c with
    | mk label state bank =>
      cases label with
      | none =>
        have hx : (used, cost, (⟨none, state, bank⟩ : Config n L S)) =
            (time, paid, ending) := Option.some.inj h
        obtain ⟨ht, hr⟩ := Prod.mk.inj hx
        obtain ⟨hc, he⟩ := Prod.mk.inj hr
        subst time
        subst paid
        subst ending
        exact ⟨0, Nat.zero_le _, (Nat.add_zero _).symm, rfl, rfl⟩
      | some label => cases h
  | succ fuel ih =>
    cases c with
    | mk label state bank =>
      cases label with
      | none =>
        have hx : (used, cost, (⟨none, state, bank⟩ : Config n L S)) =
            (time, paid, ending) := Option.some.inj h
        obtain ⟨ht, hr⟩ := Prod.mk.inj hx
        obtain ⟨hc, he⟩ := Prod.mk.inj hr
        subst time
        subst paid
        subst ending
        exact ⟨0, Nat.zero_le _, (Nat.add_zero _).symm, rfl, rfl⟩
      | some label =>
        let first := exec e (program label) state bank
        have hh : seek e program fuel (used + 1) (cost + first.1) first.2 =
            some (time, paid, ending) := h
        obtain ⟨steps, hs, ht, hm, he⟩ := ih (used + 1) (cost + first.1) first.2 hh
        refine ⟨steps + 1, Nat.succ_le_succ hs, ?_, ?_, he⟩
        · calc
            time = (used + 1) + steps := ht
            _ = used + (1 + steps) := Nat.add_assoc _ _ _
            _ = used + (steps + 1) := congrArg (Nat.add used) (Nat.add_comm 1 steps)
        · change measure e program steps (cost + first.1) (some first.2) = _
          exact hm

/-- A successful single-pass observation records the exact canonical primitive
run on the original TM2 configuration, including every physical stack. -/
theorem seek_correct (e : Fin n ≃ K) (program : Program (K := K) (L := L) (S := S))
    (fuel : ℕ) (c : Config n L S) (time paid : ℕ) (ending : Config n L S)
    (h : seek e program fuel 0 0 c = some (time, paid, ending)) :
    time ≤ fuel ∧ ending.l = none ∧
      GraphPreprocessing.Primitive.run program time (some (toCfg e c)) =
        (paid, some (toCfg e ending)) := by
  obtain ⟨steps, hs, ht, hm, he⟩ := seek_measure e program fuel 0 0 c time paid ending h
  have htime : time = steps := by simpa only [Nat.zero_add] using ht
  rw [htime]
  refine ⟨hs, he, ?_⟩
  have hr := measure_eq e program steps 0 (some c)
  rw [hm] at hr
  simpa only [Nat.zero_add, Option.map_some] using hr.symm

end Counting.Algorithm.KarpLubyRequest.Whole.ArrayPrimitive
