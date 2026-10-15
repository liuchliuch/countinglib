import Counting.Algorithm.VariableEliminationWork.Cost
import Counting.Algorithm.VariableElimination.Program

/-! # Factor occurrences whose actual callbacks retain observations -/

namespace Counting.Algorithm.VariableEliminationWork

open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationLayout

variable {V D R : Type} {q : Nat}

/-- Every occurrence owns an observed local reader. The scope retains ordered
ports and multiplicity; the reader is invoked by the measured executor itself. -/
structure ObservedFactor (V D R : Type) where
  arity : Nat
  scope : Fin arity → V
  read : (Fin arity → D) → Observed R

namespace ObservedFactor

def erase (f : ObservedFactor V D R) : Factor V D R :=
  ⟨f.arity, f.scope, fun a => (f.read a).value⟩

def oracle (f : Factor V D R) : ObservedFactor V D R :=
  ⟨f.arity, f.scope, fun a => ⟨f.value a, {oracleCalls := 1}⟩⟩

@[simp] theorem erase_oracle (f : Factor V D R) : (oracle f).erase = f := by
  cases f; rfl

/-- Capture one prepared cached reader. Its work is returned at every read;
preparation takes place outside the callback and is charged once by `prepare`. -/
def fromCache {n : Nat} (scope : Fin n → V) (cache : CachedTable (Fin n) (Fin q) R) :
    ObservedFactor V (Fin q) R :=
  ⟨n, scope, fun a => let r := cache.readFin a; ⟨r.value, {reads := r.work}⟩⟩

@[simp] theorem erase_fromCache {n : Nat} (scope : Fin n → V)
    (cache : CachedTable (Fin n) (Fin q) R) :
    (fromCache scope cache).erase = ⟨n, scope, cache.table.evalIndexed⟩ := by
  have h : (fun a => (cache.readFin a).value) = cache.table.evalIndexed := by
    funext a
    exact (cache.evalFin_eq_eval a).trans (cache.eval_eq_evalIndexed a)
  exact congrArg (fun value => (⟨n, scope, value⟩ : Factor V (Fin q) R)) h

@[simp] theorem work_fromCache {n : Nat} (scope : Fin n → V)
    (cache : CachedTable (Fin n) (Fin q) R) (a : Fin n → Fin q) :
    ((fromCache scope cache).read a).work =
      {reads := ⟨n + 1, 0, 0, 0, n, n, 1⟩} := by
  simp only [fromCache, CachedTable.work_readFin, Fintype.card_fin]

/-- The old array is reused, and actual generated layout preparation is retained. -/
def prepare (f : TabulatedFactor V (Fin q) R) : Observed (ObservedFactor V (Fin q) R) :=
  let prepared := cacheFinTable f.table
  ⟨fromCache f.scope prepared.cache,
    (Work.ofCachePreparation prepared).add {closureConstructions := 1}⟩

@[simp] theorem erase_prepare (f : TabulatedFactor V (Fin q) R) :
    (prepare f).value.erase = f.toFactor := by
  simp only [prepare, erase_fromCache, table_cacheFinTable, TabulatedFactor.toFactor]

/-- Relabel an unrelated occurrence while retaining its exact observed reader. -/
def retain [DecidableEq V] (v : V) (f : ObservedFactor V D R)
    (h : v ∉ f.erase.support) : ObservedFactor (Remaining v) D R :=
  ⟨f.arity, fun i => ⟨f.scope i, fun hi => h ((Factor.mem_support _ _).mpr ⟨i, hi⟩)⟩,
    f.read⟩

@[simp] theorem erase_retain [LinearOrder V] (v : V) (f : ObservedFactor V D R)
    (h : v ∉ f.erase.support) :
    (f.retain v h).erase = Counting.Algorithm.VariableElimination.retain v f.erase h := rfl

@[simp] theorem read_retain [DecidableEq V] (v : V) (f : ObservedFactor V D R)
    (h : v ∉ f.erase.support) : (f.retain v h).read = f.read := rfl

end ObservedFactor

def erase (fs : List (ObservedFactor V D R)) : List (Factor V D R) :=
  fs.map ObservedFactor.erase

/-- Selected occurrence states keep their real readers, not merely their values. -/
def selected [DecidableEq V] (v : V) (fs : List (ObservedFactor V D R)) :
    List (ObservedFactor V D R) := fs.filter (fun f => v ∈ f.erase.support)

@[simp] theorem erase_selected [Fintype V] [LinearOrder V]
    (v : V) (fs : List (ObservedFactor V D R)) :
    erase (selected v fs) = bucket v (erase fs) := by
  simp [erase, selected, bucket, List.filter_map, Function.comp_def]

/-- Each selected observed occurrence determines an occurrence in the semantic
bucket. Proofs do not search for equal coefficient functions at runtime. -/
def semanticMember [Fintype V] [LinearOrder V] (v : V)
    (fs : List (ObservedFactor V D R)) (f : {f // f ∈ selected v fs}) :
    {f // f ∈ bucket v (erase fs)} :=
  ⟨f.val.erase, by rw [← erase_selected]; exact List.mem_map.mpr ⟨f.val, f.property, rfl⟩⟩

theorem attach_bucket [Fintype V] [LinearOrder V] (v : V)
    (fs : List (ObservedFactor V D R)) :
    (bucket v (erase fs)).attach = (selected v fs).attach.map (semanticMember v fs) := by
  apply List.map_injective_iff.mpr Subtype.val_injective
  simp only [List.attach_map_subtype_val, List.map_map, semanticMember, Function.comp_def]
  change bucket v (erase fs) = (selected v fs).attach.map (fun f => f.val.erase)
  rw [List.attach_map_val]
  exact (erase_selected v fs).symm

end Counting.Algorithm.VariableEliminationWork
