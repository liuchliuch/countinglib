import Counting.Computation.PolyTime
import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.OfFn

set_option backward.isDefEq.respectTransparency false

/-!
# Finite symbol-expansion machines

The scan/reverse architecture is adapted from the inspected upstream
`PlanarHom.RawBooleanListMachine`; this module reconstructs and generalizes the
small machine directly over the locked F1 TM2 interface. Every source symbol
selects one fixed finite statement, and every generated symbol is transferred
through a real stack transition before halting.
-/

namespace Counting.GraphCSP.Machine

open Turing Turing.TM2 Computability

inductive Stack | input | buffer | output
  deriving DecidableEq, Fintype

inductive Label | scan | reverse | finish
  deriving DecidableEq, Fintype

variable {Γ Δ : Type}

abbrev alphabet (Γ Δ : Type) : Stack → Type
  | .input => Γ
  | .buffer => Δ
  | .output => Δ

def store (xs : List Γ) (buf out : List Δ) : ∀ k, List (alphabet Γ Δ k)
  | .input => xs
  | .buffer => buf
  | .output => out

abbrev State (Γ Δ : Type) := Option Γ × Option Δ
abbrev Instruction (Γ Δ : Type) := Stmt (alphabet Γ Δ) Label (State Γ Δ)

/-- A fixed word is compiled into finitely many literal pushes. -/
def pushWord : List Δ → Instruction Γ Δ → Instruction Γ Δ
  | [], q => q
  | b :: bs, q => .push .buffer (fun _ => b) (pushWord bs q)

theorem pushWord_correct (bs : List Δ) (q : Instruction Γ Δ)
    (v : State Γ Δ) (xs : List Γ) (buf out : List Δ) :
    stepAux (pushWord bs q) v (store xs buf out) =
      stepAux q v (store xs (bs.reverse ++ buf) out) := by
  induction bs generalizing buf with
  | nil => rfl
  | cons b bs ih =>
      change stepAux (pushWord bs q) v
        (Function.update (store xs buf out) Stack.buffer (b :: buf)) = _
      have he : Function.update (store xs buf out) Stack.buffer (b :: buf) =
          store xs (b :: buf) out := by
        funext k; cases k <;> simp [store]
      rw [he, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- The continuation always resets both finite registers. -/
def scanAgain : Instruction Γ Δ :=
  .load (fun _ => (none, none)) (.goto (fun _ => .scan))

/-- Dispatch is a finite syntax tree, not an unbounded lookup primitive. -/
def dispatch [DecidableEq Γ] (word : Γ → List Δ) : List Γ → Instruction Γ Δ
  | [] => scanAgain
  | a :: as => .branch (fun v => decide (v.1 = some a))
      (pushWord (word a) scanAgain) (dispatch word as)

theorem dispatch_correct [DecidableEq Γ] (word : Γ → List Δ)
    (as : List Γ) (a : Γ) (ha : a ∈ as) (o : Option Δ)
    (xs : List Γ) (buf out : List Δ) :
    stepAux (dispatch word as) (some a, o) (store xs buf out) =
      ⟨some .scan, (none, none), store xs ((word a).reverse ++ buf) out⟩ := by
  induction as with
  | nil => cases ha
  | cons b as ih =>
      by_cases hab : a = b
      · subst b
        simp only [dispatch, stepAux, decide_true, Bool.cond_true]
        rw [pushWord_correct]
        rfl
      · simp only [dispatch, stepAux, Option.some.injEq, hab, decide_false,
          Bool.cond_false]
        exact ih (by simpa [List.mem_cons, hab] using ha)

noncomputable def symbols (Γ : Type) [Fintype Γ] : List Γ := Finset.univ.toList

@[simp] theorem mem_symbols [Fintype Γ] (a : Γ) : a ∈ symbols Γ := by
  classical
  simp [symbols]

/-- Three labels suffice: scan and expand, reverse, and halt. -/
noncomputable def program [Fintype Γ] [DecidableEq Γ] [Inhabited Δ]
    (word : Γ → List Δ) : Label → Instruction Γ Δ
  | .scan => .pop .input (fun v a => (a, v.2))
      (.branch (fun v => v.1.isSome)
        (dispatch word (symbols Γ))
        (.load (fun _ => (none, none)) (.goto (fun _ => .reverse))))
  | .reverse => .pop .buffer (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome)
        (.push .output (fun v => v.2.getD default)
          (.load (fun _ => (none, none)) (.goto (fun _ => .reverse))))
        (.load (fun _ => (none, none)) (.goto (fun _ => .finish))))
  | .finish => .halt

noncomputable def machine [Fintype Γ] [DecidableEq Γ] [Fintype Δ] [Inhabited Δ]
    (word : Γ → List Δ) : FinTM2 where
  K := Stack
  Γ := alphabet Γ Δ
  k₀ := .input
  k₁ := .output
  Λ := Label
  main := .scan
  σ := State Γ Δ
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype Γ)
  m := program word

variable [Fintype Γ] [DecidableEq Γ] [Fintype Δ] [Inhabited Δ]

noncomputable def cfg (word : Γ → List Δ) (l : Label)
    (xs : List Γ) (buf out : List Δ) : (machine word).Cfg :=
  ⟨some l, (none, none), store xs buf out⟩

noncomputable abbrev iter (word : Γ → List Δ) (n : ℕ) (c : (machine word).Cfg) :
    Option (machine word).Cfg :=
  (fun c : Option (machine word).Cfg => c.bind (machine word).step)^[n] (some c)

theorem step_scan_nil (word : Γ → List Δ) (buf out : List Δ) :
    (machine word).step (cfg word .scan [] buf out) =
      some (cfg word .reverse [] buf out) := by
  simp only [machine, FinTM2.step, cfg, step, program, stepAux, store,
    List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
  congr 2
  funext k; cases k <;> simp [store]

theorem step_scan_cons (word : Γ → List Δ) (a : Γ)
    (xs : List Γ) (buf out : List Δ) :
    (machine word).step (cfg word .scan (a :: xs) buf out) =
      some (cfg word .scan xs ((word a).reverse ++ buf) out) := by
  simp only [machine, FinTM2.step, cfg, step, program, stepAux, store,
    List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons]
  have he : Function.update (store (a :: xs) buf out) Stack.input xs =
      store xs buf out := by
    funext k; cases k <;> simp [store]
  change some (stepAux (dispatch word (symbols Γ)) (some a, none)
    (Function.update (store (a :: xs) buf out) Stack.input xs)) = _
  rw [he, dispatch_correct word (symbols Γ) a (mem_symbols a)]

theorem scan_run (word : Γ → List Δ) (xs : List Γ) (buf out : List Δ) :
    iter word (xs.length + 1) (cfg word .scan xs buf out) =
      some (cfg word .reverse [] ((xs.flatMap word).reverse ++ buf) out) := by
  induction xs generalizing buf with
  | nil => simpa [iter] using step_scan_nil word buf out
  | cons a xs ih =>
      change (fun c : Option (machine word).Cfg => c.bind (machine word).step)^[xs.length + 1 + 1]
        (some (cfg word .scan (a :: xs) buf out)) = _
      rw [Function.iterate_succ_apply]
      change (fun c : Option (machine word).Cfg => c.bind (machine word).step)^[xs.length + 1]
        ((machine word).step (cfg word .scan (a :: xs) buf out)) = _
      rw [step_scan_cons]
      simpa only [List.flatMap_cons, List.reverse_append, List.append_assoc]
        using ih ((word a).reverse ++ buf)

theorem step_reverse_nil (word : Γ → List Δ) (out : List Δ) :
    (machine word).step (cfg word .reverse [] [] out) =
      some (cfg word .finish [] [] out) := by
  simp only [machine, FinTM2.step, cfg, step, program, stepAux, store,
    List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
  congr 2
  funext k; cases k <;> simp [store]

theorem step_reverse_cons (word : Γ → List Δ) (b : Δ) (buf out : List Δ) :
    (machine word).step (cfg word .reverse [] (b :: buf) out) =
      some (cfg word .reverse [] buf (b :: out)) := by
  simp only [machine, FinTM2.step, cfg, step, program, stepAux, store,
    List.head?_cons, Option.isSome_some, Bool.cond_true, List.tail_cons, Option.getD_some]
  congr 2
  funext k; cases k <;> simp [store]

theorem reverse_run (word : Γ → List Δ) (buf out : List Δ) :
    iter word (buf.length + 1) (cfg word .reverse [] buf out) =
      some (cfg word .finish [] [] (buf.reverse ++ out)) := by
  induction buf generalizing out with
  | nil => simpa [iter] using step_reverse_nil word out
  | cons b buf ih =>
      change (fun c : Option (machine word).Cfg => c.bind (machine word).step)^[buf.length + 1 + 1]
        (some (cfg word .reverse [] (b :: buf) out)) = _
      rw [Function.iterate_succ_apply]
      change (fun c : Option (machine word).Cfg => c.bind (machine word).step)^[buf.length + 1]
        ((machine word).step (cfg word .reverse [] (b :: buf) out)) = _
      rw [step_reverse_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (b :: out)

theorem finish_run (word : Γ → List Δ) (out : List Δ) :
    (machine word).step (cfg word .finish [] [] out) =
      some (haltList (machine word) out) := by
  simp only [machine, FinTM2.step, cfg, step, program, stepAux, haltList]
  congr 2
  funext k; cases k <;> simp [store]

theorem initial_eq (word : Γ → List Δ) (xs : List Γ) :
    initList (machine word) xs = cfg word .scan xs [] [] := by
  unfold initList cfg
  congr 1
  funext k; cases k <;> simp [machine, store]

/-- Exact run length includes all scan transitions, output reversal, and halt. -/
theorem flatMap_run (word : Γ → List Δ) (xs : List Γ) :
    (fun c : Option (machine word).Cfg => c.bind (machine word).step)^[
      xs.length + (xs.flatMap word).length + 3]
      (some (initList (machine word) xs)) =
        some (haltList (machine word) (xs.flatMap word)) := by
  have h₁ : iter word (xs.length + 1) (cfg word .scan xs [] []) =
      some (cfg word .reverse [] (xs.flatMap word).reverse []) := by
    simpa only [List.append_nil] using scan_run word xs [] []
  have h₂ : iter word ((xs.flatMap word).reverse.length + 1)
      (cfg word .reverse [] (xs.flatMap word).reverse []) =
      some (cfg word .finish [] [] (xs.flatMap word)) := by
    simpa only [List.reverse_reverse, List.append_nil] using
      reverse_run word (xs.flatMap word).reverse []
  have h₃ : iter word 1 (cfg word .finish [] [] (xs.flatMap word)) =
      some (haltList (machine word) (xs.flatMap word)) := finish_run word _
  have hlen : 1 + (((xs.flatMap word).reverse.length + 1) + (xs.length + 1)) =
      xs.length + (xs.flatMap word).length + 3 := by
    simp only [List.length_reverse]
    omega
  unfold iter at h₁ h₂ h₃
  rw [initial_eq, ← hlen, Function.iterate_add_apply, Function.iterate_add_apply, h₁, h₂]
  exact h₃

/-- A fixed syntax-derived upper bound on each symbol's emitted word. -/
noncomputable def expansionBound (word : Γ → List Δ) : ℕ :=
  ∑ a : Γ, (word a).length

omit [DecidableEq Γ] [Fintype Δ] [Inhabited Δ] in
theorem word_length_le (word : Γ → List Δ) (a : Γ) :
    (word a).length ≤ expansionBound word := by
  exact Finset.single_le_sum (f := fun a => (word a).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

omit [DecidableEq Γ] [Fintype Δ] [Inhabited Δ] in
theorem flatMap_length_le (word : Γ → List Δ) (xs : List Γ) :
    (xs.flatMap word).length ≤ expansionBound word * xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
      have ha := word_length_le word a
      omega

/-- Compile a proved serialization equation into a concrete finite TM2. The
hypothesis equates two independently supplied serialized values; no machine or
runtime bound is assumed. -/
noncomputable def flatMapPolyTime {A B : Type}
    (ea : Encoding A Γ) (eb : Encoding B Δ) (f : A → B) (word : Γ → List Δ)
    (correct : ∀ a, eb.encode (f a) = (ea.encode a).flatMap word) :
    Counting.Computation.PolyTime ea eb f where
  tm := machine word
  inputAlphabet := Equiv.refl Γ
  outputAlphabet := Equiv.refl Δ
  time := Polynomial.C (1 + expansionBound word) * Polynomial.X + Polynomial.C 3
  outputsFun a := {
    steps := (ea.encode a).length + ((ea.encode a).flatMap word).length + 3
    evals_in_steps := by
      change (fun c : Option (machine word).Cfg => c.bind (machine word).step)^[
          (ea.encode a).length + ((ea.encode a).flatMap word).length + 3]
        (some (initList (machine word) ((ea.encode a).map id))) =
          some (haltList (machine word) ((eb.encode (f a)).map id))
      rw [List.map_id, List.map_id, correct]
      exact flatMap_run word _
    steps_le_m := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      have h := flatMap_length_le word (ea.encode a)
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
        Nat.add_le_add_left (Nat.add_le_add_right h 3) (ea.encode a).length }
  finiteAlphabets k := by cases k <;> dsimp [machine, alphabet] <;> infer_instance

@[simp] theorem flatMapPolyTime_steps {A B : Type}
    (ea : Encoding A Γ) (eb : Encoding B Δ) (f : A → B) (word : Γ → List Δ)
    (correct : ∀ a, eb.encode (f a) = (ea.encode a).flatMap word) (a : A) :
    ((flatMapPolyTime ea eb f word correct).outputsFun a).steps =
      (ea.encode a).length + ((ea.encode a).flatMap word).length + 3 := rfl

/-- Symbol renaming is implemented by the same scan/reverse machine with one
literal push per source symbol, and the sharp linear bound `2 n + 3`. -/
noncomputable def mapPolyTime {A B : Type}
    (ea : Encoding A Γ) (eb : Encoding B Δ) (f : A → B) (rename : Γ → Δ)
    (correct : ∀ a, eb.encode (f a) = (ea.encode a).map rename) :
    Counting.Computation.PolyTime ea eb f where
  tm := machine (fun a => [rename a])
  inputAlphabet := Equiv.refl Γ
  outputAlphabet := Equiv.refl Δ
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun a := {
    steps := 2 * (ea.encode a).length + 3
    evals_in_steps := by
      have h := flatMap_run (fun a => [rename a]) (ea.encode a)
      have hflat : (ea.encode a).flatMap (fun a => [rename a]) =
          (ea.encode a).map rename := by
        induction ea.encode a with
        | nil => rfl
        | cons b bs ih => simp only [List.flatMap_cons, List.map_cons,
            List.singleton_append, ih]
      rw [hflat, List.length_map] at h
      change (fun c : Option (machine (fun a => [rename a])).Cfg =>
          c.bind (machine (fun a => [rename a])).step)^[2 * (ea.encode a).length + 3]
        (some (initList (machine (fun a => [rename a])) ((ea.encode a).map id))) =
          some (haltList (machine (fun a => [rename a])) ((eb.encode (f a)).map id))
      simpa only [List.map_id, correct, two_mul] using h
    steps_le_m := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      exact Nat.le_refl _ }
  finiteAlphabets k := by cases k <;> dsimp [machine, alphabet] <;> infer_instance

@[simp] theorem mapPolyTime_steps {A B : Type}
    (ea : Encoding A Γ) (eb : Encoding B Δ) (f : A → B) (rename : Γ → Δ)
    (correct : ∀ a, eb.encode (f a) = (ea.encode a).map rename) (a : A) :
    ((mapPolyTime ea eb f rename correct).outputsFun a).steps =
      2 * (ea.encode a).length + 3 := rfl

@[simp] theorem mapPolyTime_time {A B : Type}
    (ea : Encoding A Γ) (eb : Encoding B Δ) (f : A → B) (rename : Γ → Δ)
    (correct : ∀ a, eb.encode (f a) = (ea.encode a).map rename) :
    (mapPolyTime ea eb f rename correct).time =
      Polynomial.C 2 * Polynomial.X + Polynomial.C 3 := rfl

end Counting.GraphCSP.Machine
