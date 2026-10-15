import Holant.Proofs.Tetrahedral.EvenCSPReduction.Program

/-! Fixed-divisor unary division by an actual finite Boolean-stack program.
Every transition consumes one physical input token. Fin k is a compile-time
phase label; the last phase emits one quotient token and returns to phase zero.
Partial groups halt without emitting a token. -/
namespace Paper2.DegreeCSP.ComputationDivide
open Holant.Complexity Holant.Complexity.BinaryCompose Holant.Complexity.GraphPreprocessing
open Computability Turing
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (k : ℕ) (hk : 0<k)

abbrev machine : Machine where
  K := Fin 2
  input := 0
  output := 1
  Label := Fin k
  main := ⟨0,hk⟩
  State := Option Bool
  initial := none
  program t := .pop 0 (fun _ b=>b) (.branch Option.isSome
    (if h : t.val+1<k then
      .load (fun _=>none) (.goto (fun _=>⟨t.val+1,h⟩))
    else .push 1 (fun _=>true) (.load (fun _=>none) (.goto (fun _=>⟨0,hk⟩)))) .halt)

def config (t : Fin k) (tokens output : List Bool) : (machine k hk).computer.Cfg :=
  ⟨some t,none,![tokens,output]⟩

theorem empty_step (t : Fin k) (output : List Bool) :
    (machine k hk).computer.step (config k hk t [] output)=
      some (haltList (machine k hk).computer output) := by
  rw [Machine.halt_eq]
  dsimp [machine,config,FinTM2.step,TM2.step,TM2.stepAux]
  simp only [List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
  congr 2
  funext j
  fin_cases j <;> rfl

theorem next_step (t : Fin k) (tokens output : List Bool) (ht : t.val+1<k) :
    (machine k hk).computer.step (config k hk t (true::tokens) output)=
      some (config k hk ⟨t.val+1,ht⟩ tokens output) := by
  dsimp [machine,config,FinTM2.step,TM2.step,TM2.stepAux]
  simp only [List.head?_cons,Option.isSome_some,Bool.cond_true,List.tail_cons,dif_pos ht]
  dsimp only [TM2.stepAux]
  congr 2
  funext j
  fin_cases j <;> rfl

theorem last_step (t : Fin k) (tokens output : List Bool) (ht : ¬t.val+1<k) :
    (machine k hk).computer.step (config k hk t (true::tokens) output)=
      some (config k hk ⟨0,hk⟩ tokens (true::output)) := by
  dsimp [machine,config,FinTM2.step,TM2.step,TM2.stepAux]
  simp only [List.head?_cons,Option.isSome_some,Bool.cond_true,List.tail_cons,dif_neg ht]
  dsimp only [TM2.stepAux]
  congr 2
  funext j
  fin_cases j <;> rfl

theorem exact_run (n : ℕ) (t : Fin k) (output : List Bool) :
    (fun c => c.bind (machine k hk).computer.step)^[n+1]
      (some (config k hk t (List.replicate n true) output))=
      some (haltList (machine k hk).computer
        (List.replicate ((n+t.val)/k) true++output)) := by
  induction n generalizing t output with
  | zero =>
    simpa [Nat.div_eq_of_lt t.isLt] using empty_step k hk t output
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [Function.comp_def,id_eq,List.replicate_succ,Option.bind_some]
    by_cases ht : t.val+1<k
    · rw [next_step k hk t _ _ ht]
      rw [ih]
      have he : n+(⟨t.val+1,ht⟩ : Fin k).val=n+1+t.val := by dsimp; omega
      rw [he]
    · rw [last_step k hk t _ _ ht]
      rw [ih]
      have ht' : t.val+1=k := by have hb:=t.isLt; omega
      have hq : (n+1+t.val)/k=n/k+1 := by
        have he : n+1+t.val=n+k := by omega
        rw [he,Nat.add_div_right _ hk]
      rw [hq]
      simp only [Fin.val_mk,Nat.add_zero,List.replicate_add,List.replicate_one,
        List.append_assoc,List.singleton_append]

def computes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (fun n=>n/k) where
  machine := machine k hk
  time := Polynomial.X+1
  outputs n := {
    steps := n+1
    evals_in_steps := by
      change (fun c : Option (machine k hk).computer.Cfg => c.bind (machine k hk).computer.step)^[n+1]
        (some (initList (machine k hk).computer (List.replicate n true)))=
          some (haltList (machine k hk).computer (List.replicate (n/k) true))
      have hi : config k hk ⟨0,hk⟩ (List.replicate n true) []=
          initList (machine k hk).computer (List.replicate n true) := by
        rw [Machine.init_eq]
        dsimp [config,machine]
        congr 1
        funext j
        fin_cases j <;> rfl
      simpa only [hi,Fin.val_mk,Nat.add_zero,List.append_nil] using
        exact_run k hk n ⟨0,hk⟩ []
    steps_le_m := by simp [UnaryBinary.unaryEncoding] }

end
end Paper2.DegreeCSP.ComputationDivide
