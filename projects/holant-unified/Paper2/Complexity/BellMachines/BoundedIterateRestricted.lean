import Paper2.Complexity.BellMachines.BoundedIterateInterface

/-! The identical bounded-iteration controller specialized to a promise on its
initial state. The promise adds no bits and is not an instruction; callers must
construct that state by an actual initializer. This is useful for powers from 1. -/
namespace Paper2.Complexity.BellMachines.BoundedIterate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines GraphPreprocessing
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
noncomputable section
variable {A : Type} (e : Encoding A Bool) (f : A → A)

def restrictedEncoding (p : ℕ × A → Prop) [DecidablePred p] :
    Encoding {x : ℕ × A // p x} Bool where
  encode x := (inputEncoding e).encode x.val
  decode bits := ((inputEncoding e).decode bits).bind
    (fun x => if h : p x then some ⟨x,h⟩ else none)
  decode_encode x := by simp [x.property]

 def restrictedOfDistinct (w : Computes e e f) (hio : w.machine.output ≠ w.machine.input)
    (p : ℕ × A → Prop) [DecidablePred p] (Q : Polynomial ℕ)
    (hb : ∀ (x : {x : ℕ × A // p x}) (k : ℕ), k ≤ x.val.1 →
      (e.encode ((f^[k]) x.val.2)).length ≤ Q.eval ((restrictedEncoding e p).encode x).length) :
    Computes (restrictedEncoding e p) e (fun x => (f^[x.val.1]) x.val.2) where
  machine := machine w.machine
  time := timePolynomial e f w Q
  outputs x := {
    steps := 2*(x.val.1+1)+2*((e.encode x.val.2).length+1)+
      ticks e f (fun a => (w.outputs a).steps) x.val.1 x.val.2
    evals_in_steps := whole e f w.machine hio _ (fun a => (w.outputs a).evals_in_steps) x.val.1 x.val.2
    steps_le_m := by
      let N := ((restrictedEncoding e p).encode x).length
      have hlen : N = 2*x.val.1+1+(e.encode x.val.2).length := by
        simp [N,restrictedEncoding,inputEncoding,pairEncoding,UnaryBinary.unaryEncoding]
      have hcnt : x.val.1 ≤ N := by omega
      have hword : (e.encode x.val.2).length ≤ N := by omega
      have ht := ticks_bound e f (fun a => (w.outputs a).steps) x.val.1 x.val.2
        (w.time.eval (Q.eval N)) (Q.eval N)
        (fun k hk => le_trans (w.outputs _).steps_le_m
          (natPolynomial_eval_mono w.time (hb x k hk)))
        (fun k hk => hb x k hk)
      have hm := Nat.mul_le_mul_right (w.time.eval (Q.eval N)+2*Q.eval N+3) hcnt
      change _ ≤ (timePolynomial e f w Q).eval N
      simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Polynomial.eval_comp]
      omega }

 def restrictedComputes (w : Computes e e f)
    (p : ℕ × A → Prop) [DecidablePred p] (Q : Polynomial ℕ)
    (hb : ∀ (x : {x : ℕ × A // p x}) (k : ℕ), k ≤ x.val.1 →
      (e.encode ((f^[k]) x.val.2)).length ≤ Q.eval ((restrictedEncoding e p).encode x).length) :
    Computes (restrictedEncoding e p) e (fun x => (f^[x.val.1]) x.val.2) := by
  let w' := congrComputes (w.andThen (identityComputes e)) (fun _ => rfl)
  exact restrictedOfDistinct e f w' (by intro h; cases h) p Q hb

end
end Paper2.Complexity.BellMachines.BoundedIterate
