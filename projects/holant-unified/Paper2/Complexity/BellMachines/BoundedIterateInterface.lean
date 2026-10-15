import Paper2.Complexity.BellMachines.BoundedIterateRun
import Paper2.Complexity.BellMachines.FixedFieldMachines.PairEncoding
import Paper2.Complexity.BellMachines.BinaryCompose.OutputBound

/-! Polynomial iteration from an actual round program and a polynomial bound
on the encoded intermediate values. The input counter is unary, so the number
of rounds is charged to real input bits. -/
namespace Paper2.Complexity.BellMachines.BoundedIterate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines GraphPreprocessing
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
noncomputable section
variable {A : Type} (e : Encoding A Bool) (f : A → A)

def ticks (steps : A → ℕ) : ℕ → A → ℕ
  | 0, _ => 2
  | n+1, a => 1 + steps a + 2*((e.encode (f a)).length+1) + ticks steps n (f a)

 theorem loop (m : Machine) (hio : m.output ≠ m.input) (steps : A → ℕ)
    (runs : ∀ a, (fun c => c.bind m.computer.step)^[steps a]
      (some (initList m.computer (e.encode a))) = some (haltList m.computer (e.encode (f a))))
    (n : ℕ) (a : A) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 4) (e.encode a) (List.replicate n true))
      (haltList (machine m).computer (e.encode ((f^[n]) a))) (ticks e f steps n a) := by
  induction n generalizing a with
  | zero =>
    exact (runsExactly_one (counter_nil m _)).trans (runsExactly_one (final_halt m _))
  | succ n ih =>
    have h := (runsExactly_one (counter_cons m (e.encode a) (List.replicate n true))).trans
      ((call m (e.encode a) (e.encode (f a)) (List.replicate n true) (steps a) (runs a)).trans
        ((reload m hio (e.encode (f a)) (List.replicate n true)).trans (ih (f a))))
    simpa only [List.replicate_succ,Function.iterate_succ_apply,ticks,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def inputEncoding : Encoding (ℕ × A) Bool := pairEncoding UnaryBinary.unaryEncoding e

 theorem whole (m : Machine) (hio : m.output ≠ m.input) (steps : A → ℕ)
    (runs : ∀ a, (fun c => c.bind m.computer.step)^[steps a]
      (some (initList m.computer (e.encode a))) = some (haltList m.computer (e.encode (f a))))
    (n : ℕ) (a : A) :
    (fun c => c.bind (machine m).computer.step)^[2*(n+1)+2*((e.encode a).length+1)+ticks e f steps n a]
      (some (initList (machine m).computer ((inputEncoding e).encode (n,a)))) =
      some (haltList (machine m).computer (e.encode ((f^[n]) a))) := by
  have h := ((prepare m (List.replicate n true) (e.encode a)).trans
    (load_word m (List.replicate n true) (e.encode a))).trans (loop e f m hio steps runs n a)
  have hi : config m (.inr 0) (fun _ => [])
      (Paper2.Algebraic.frame (List.replicate n true) ++ e.encode a) [] [] =
      initList (machine m).computer ((inputEncoding e).encode (n,a)) := by
    rw [Machine.init_eq]
    change cfg (.inr 0 : Label m) m.initial _ = ⟨some (.inr 0),(none,m.initial),_⟩
    congr 1
    funext k
    rcases k with k | k
    · simp [config,tapes,wordTape,machine,inputKey]
    · fin_cases k <;> simp [config,tapes,extras,wordTape,machine,inputKey,inputEncoding,
        pairEncoding,UnaryBinary.unaryEncoding]
  change RunsExactly (TM2.step (program m))
    (initList (machine m).computer ((inputEncoding e).encode (n,a)))
    (haltList (machine m).computer (e.encode ((f^[n]) a))) _
  simpa only [hi,List.length_replicate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

 theorem ticks_bound (steps : A → ℕ) (n : ℕ) (a : A) (T S : ℕ)
    (hs : ∀ k ≤ n, steps ((f^[k]) a) ≤ T)
    (hl : ∀ k ≤ n, (e.encode ((f^[k]) a)).length ≤ S) :
    ticks e f steps n a ≤ n*(T+2*S+3)+2 := by
  induction n generalizing a with
  | zero => simp [ticks]
  | succ n ih =>
    have hzero := hs 0 (by omega)
    have hone := hl 1 (by omega)
    have hh := ih (f a)
      (fun k hk => by simpa only [Function.iterate_succ_apply] using hs (k+1) (by omega))
      (fun k hk => by simpa only [Function.iterate_succ_apply] using hl (k+1) (by omega))
    simp only [Function.iterate_zero_apply,Function.iterate_one, ticks,Nat.add_mul,Nat.one_mul] at *
    omega

/-- The bound concerns actual canonical encoded intermediate values, not an
arbitrary size annotation or a bound on the final value alone. -/
def IntermediateBound (Q : Polynomial ℕ) : Prop :=
  ∀ (n : ℕ) (a : A) (k : ℕ), k ≤ n →
    (e.encode ((f^[k]) a)).length ≤ Q.eval (((inputEncoding e).encode (n,a)).length)

 def timePolynomial (w : Computes e e f) (Q : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X * (w.time.comp Q + 2*Q + 3) + 4*Polynomial.X + 6

 def computesOfDistinct (w : Computes e e f) (hio : w.machine.output ≠ w.machine.input)
    (Q : Polynomial ℕ) (hb : IntermediateBound e f Q) :
    Computes (inputEncoding e) e (fun x => (f^[x.1]) x.2) where
  machine := machine w.machine
  time := timePolynomial e f w Q
  outputs x := {
    steps := 2*(x.1+1)+2*((e.encode x.2).length+1)+ticks e f (fun a => (w.outputs a).steps) x.1 x.2
    evals_in_steps := whole e f w.machine hio _ (fun a => (w.outputs a).evals_in_steps) x.1 x.2
    steps_le_m := by
      let N := ((inputEncoding e).encode x).length
      have hlen : N = 2*x.1+1+(e.encode x.2).length := by
        simp [N,inputEncoding,pairEncoding,UnaryBinary.unaryEncoding]
      have hcnt : x.1 ≤ N := by omega
      have hword : (e.encode x.2).length ≤ N := by omega
      have ht := ticks_bound e f (fun a => (w.outputs a).steps) x.1 x.2
        (w.time.eval (Q.eval N)) (Q.eval N)
        (fun k hk => le_trans (w.outputs _).steps_le_m
          (natPolynomial_eval_mono w.time (hb x.1 x.2 k hk)))
        (fun k hk => hb x.1 x.2 k hk)
      have hm := Nat.mul_le_mul_right (w.time.eval (Q.eval N)+2*Q.eval N+3) hcnt
      change _ ≤ (timePolynomial e f w Q).eval N
      simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Polynomial.eval_comp]
      omega }

/-- Input/output aliasing of the round program is handled by a real identity
composition on disjoint stacks, rather than assumed away. -/
 def computes (w : Computes e e f) (Q : Polynomial ℕ) (hb : IntermediateBound e f Q) :
    Computes (inputEncoding e) e (fun x => (f^[x.1]) x.2) := by
  let w' := congrComputes (w.andThen (identityComputes e)) (fun _ => rfl)
  exact computesOfDistinct e f w' (by intro h; cases h) Q hb

end
end Paper2.Complexity.BellMachines.BoundedIterate
