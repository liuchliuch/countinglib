import Counting.Algorithm.KarpLubyRequest.Dense.Allocate
import Counting.Algorithm.KarpLubyRequest.CountedList

/-!
# Finite control for a checked dense-row write

The index is a binary stack. Every decrement follows consumption of an actual
pair of row symbols. Prefix restoration retains coordinate order. Both conflict
and out-of-bounds exits clear the row, index, and pref stacks. The only extra
control datum is the Boolean literal being written.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Write
open Turing Computability Holant.Complexity StackProtocol
open Turing.TM2.Stmt

variable {K Λ τ : Type} [DecidableEq K]
abbrev Stacks (K : Type) := Fin 4 ↪ K

/-- Row, binary index, reversed row pref, borrow scratch. -/
abbrev tapes (st : Stacks K) (frame : K → List Bool)
    (row counter pref scratch : List Bool) : K → List Bool :=
  Allocate.tapes st frame row counter pref scratch

@[simp] theorem tapes_at (st : Stacks K) (frame : K → List Bool)
    (row counter pref scratch : List Bool) (i : Fin 4) :
    tapes st frame row counter pref scratch (st i) =
      (![row, counter, pref, scratch] : Fin 4 → List Bool) i :=
  Allocate.tapes_at st frame row counter pref scratch i

@[simp] theorem update_row (st : Stacks K) (frame : K → List Bool)
    (row counter pref scratch word : List Bool) :
    Function.update (tapes st frame row counter pref scratch) (st 0) word =
      tapes st frame word counter pref scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, Allocate.tapes, Function.update_apply, st.injective.eq_iff]

@[simp] theorem update_counter (st : Stacks K) (frame : K → List Bool)
    (row counter pref scratch word : List Bool) :
    Function.update (tapes st frame row counter pref scratch) (st 1) word =
      tapes st frame row word pref scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, Allocate.tapes, Function.update_apply, st.injective.eq_iff]

@[simp] theorem update_prefix (st : Stacks K) (frame : K → List Bool)
    (row counter pref scratch word : List Bool) :
    Function.update (tapes st frame row counter pref scratch) (st 2) word =
      tapes st frame row counter word scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, Allocate.tapes, Function.update_apply, st.injective.eq_iff]

@[simp] theorem update_scratch (st : Stacks K) (frame : K → List Bool)
    (row counter pref scratch word : List Bool) :
    Function.update (tapes st frame row counter pref scratch) (st 3) word =
      tapes st frame row counter pref word := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, Allocate.tapes, Function.update_apply, st.injective.eq_iff]

structure Labels (Λ : Type) where
  loop : Λ
  skip : Λ
  borrow : Λ
  restoreCounter : Λ
  write : Λ
  restoreRow : Λ
  clearCounter : Λ
  clearPrefix : Λ
  clearRow : Λ
  good : Λ
  bad : Λ

def checkStmt (row counter : K) (skip write bad : Λ) : Stmt K Λ (Bool × τ) :=
  peek row (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (peek counter (fun v b => (b, v.2))
        (branch (fun v => v.1.isSome)
          (load (fun v => (none, v.2)) (goto (fun _ => skip)))
          (load (fun v => (none, v.2)) (goto (fun _ => write)))))
      (load (fun v => (none, v.2)) (goto (fun _ => bad))))

def skipStmt (row pref : K) (next : Λ) : Stmt K Λ (Bool × τ) :=
  pop row (fun v b => (b, v.2))
    (push pref (fun v => v.1.getD false)
      (pop row (fun v b => (b, v.2))
        (push pref (fun v => v.1.getD false)
          (load (fun v => (none, v.2)) (goto (fun _ => next))))))

def writeStmt (row : K) (restore bad : Λ) : Stmt K Λ (Bool × τ) :=
  pop row (fun v b => (b, v.2))
    (branch (fun v => v.1.getD false)
      (pop row (fun v b => (b, v.2))
        (branch (fun v => v.1 == some v.2.1)
          (push row (fun v => v.2.1) (push row (fun _ => true)
            (load (fun v => (none, v.2)) (goto (fun _ => restore)))))
          (load (fun v => (none, v.2)) (goto (fun _ => bad)))))
      (pop row (fun v b => (b, v.2))
        (push row (fun v => v.2.1) (push row (fun _ => true)
          (load (fun v => (none, v.2)) (goto (fun _ => restore)))))))

structure Executes (step : Cfg K Λ (Bool × τ) → Option (Cfg K Λ (Bool × τ)))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  loop : ExecutesAt step lab.loop
    (checkStmt (st 0) (st 1) lab.skip lab.write lab.clearCounter)
  skip : ExecutesAt step lab.skip (skipStmt (st 0) (st 2) lab.borrow)
  borrow : ExecutesAt step lab.borrow
    (CountedList.Counter.decrementStmt (st 1) (st 3) lab.borrow lab.restoreCounter)
  restoreCounter : ExecutesAt step lab.restoreCounter
    (copyMoveStmt (st 3) (st 1) lab.restoreCounter lab.loop)
  write : ExecutesAt step lab.write (writeStmt (st 0) lab.restoreRow lab.clearCounter)
  restoreRow : ExecutesAt step lab.restoreRow
    (copyMoveStmt (st 2) (st 0) lab.restoreRow lab.good)
  clearCounter : ExecutesAt step lab.clearCounter
    (clearStmt (st 1) lab.clearCounter lab.clearPrefix)
  clearPrefix : ExecutesAt step lab.clearPrefix
    (clearStmt (st 2) lab.clearPrefix lab.clearRow)
  clearRow : ExecutesAt step lab.clearRow (clearStmt (st 0) lab.clearRow lab.bad)

end Counting.Algorithm.KarpLubyRequest.Dense.Write
