import Counting.Algorithm.VariableEliminationWork.Inputs
import Counting.Algorithm.VariableEliminationWork.Algebra

/-!
# Closed stored-reader contracts and whole-run operation composition

The stored-input evaluator establishes these contracts from real prepared cached
tables. They are not assumptions imposed on an arbitrary semantic value callback.
Generic observed callbacks remain available with their own explicit work model.
-/

namespace Counting.Algorithm.VariableEliminationWork

open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationLayout

variable {V R : Type} {q : Nat}

/-- Exact work of one installed cached Fin reader on an `n`-port table. -/
def cachedReadWork (n : Nat) : Work := {reads := ⟨n + 1, 0, 0, 0, n, n, 1⟩}

/-- A representation invariant proved by table preparation and materialization. -/
def ObservedFactor.IsCached (f : ObservedFactor V (Fin q) R) : Prop :=
  ∀ a, (f.read a).work = cachedReadWork f.arity

def CachedState (fs : List (ObservedFactor V (Fin q) R)) : Prop :=
  ∀ f ∈ fs, f.IsCached

@[simp] theorem isCached_fromCache {n : Nat} (scope : Fin n → V)
    (cache : CachedTable (Fin n) (Fin q) R) :
    (ObservedFactor.fromCache scope cache).IsCached :=
  ObservedFactor.work_fromCache scope cache

@[simp] theorem isCached_prepare (f : TabulatedFactor V (Fin q) R) :
    (ObservedFactor.prepare f).value.IsCached := isCached_fromCache _ _

@[simp] theorem isCached_compileRows (f : ObservedFactor V (Fin q) R)
    (rows : List (Fin f.arity → Fin q))
    (h : rows = enumerateAssignments (Fin f.arity) (Fin q)) :
    (compileRows f rows h).value.IsCached := isCached_prepare _

@[simp] theorem isCached_compile (f : ObservedFactor V (Fin q) R) :
    (compile f).value.IsCached := isCached_compileRows _ _ _

theorem isCached_retain [LinearOrder V] (v : V) (f : ObservedFactor V (Fin q) R)
    (h : v ∉ f.erase.support) (hf : f.IsCached) : (f.retain v h).IsCached := hf

theorem cachedState_retainAll [LinearOrder V] (v : V)
    (fs : List (ObservedFactor V (Fin q) R)) (h : CachedState fs) :
    CachedState (retainAll v fs).value := by
  induction fs with
  | nil => simp [retainAll, CachedState]
  | cons f fs ih =>
      have hf := h f (by simp)
      have ht : CachedState fs := fun g hg => h g (by simp [hg])
      simp only [retainAll]
      split
      · exact ih ht
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact isCached_retain _ _ _ hf
        · exact ih ht g hg

@[simp] theorem cachedState_prepareInputs (fs : List (TabulatedFactor V (Fin q) R)) :
    CachedState (prepareInputs fs).value := by
  induction fs with
  | nil => simp [prepareInputs, CachedState]
  | cons f fs ih =>
      intro g hg
      simp only [prepareInputs, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact isCached_prepare f
      · exact ih g hg

theorem cachedState_step [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) (h : CachedState fs) :
    CachedState (step v fs).value := by
  intro f hf
  simp only [step, List.mem_cons] at hf
  rcases hf with rfl | hf
  · exact isCached_compile _
  · exact cachedState_retainAll v fs h f hf

/-- The sum of the distinct occurrence readers; repeated factors and repeated
ports contribute separately. -/
def factorReadWork (fs : List (ObservedFactor V (Fin q) R)) : Work :=
  Work.sum (fs.map (fun f => cachedReadWork f.arity))

def productWork (fs : List (ObservedFactor V (Fin q) R)) : Work :=
  (factorReadWork fs).add {coefficientMultiplications := fs.length, listCases := fs.length + 1}

/-- A closed expression for one pivot-sum row, derived from the actual nested
callback loops, with separate coefficient and address components. -/
def rowWork (q : Nat) (fs : List (ObservedFactor V (Fin q) R)) : Work :=
  (Work.scale q (productWork fs)).add {coefficientAdditions := q, listCases := q + 1}

theorem work_bucketProduct_cached [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) (h : CachedState fs)
    (d : Fin q) (a : Fin (bucketVars v (erase fs)).length → Fin q) :
    (bucketProduct v fs d a).work = productWork (selected v fs) := by
  rw [work_bucketProduct]
  unfold productWork factorReadWork
  congr 1
  congr 1
  calc
    _ = (selected v fs).attach.map (fun f => cachedReadWork f.val.arity) := by
      apply List.map_congr_left
      intro f _
      exact h f.val (List.mem_of_mem_filter f.property) _
    _ = _ := List.attach_map_val (f := fun f : ObservedFactor V (Fin q) R => cachedReadWork f.arity)

theorem work_bucketSum_cached [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) (h : CachedState fs)
    (a : Fin (bucketVars v (erase fs)).length → Fin q) :
    (bucketSum v fs (generateFinRange q).values a).work = rowWork q (selected v fs) := by
  rw [work_bucketSum]
  simp only [work_bucketProduct_cached v fs h, Work.sum_const,
    generateFinRange_length, rowWork]

/-- Endpoint observations include all remaining cached scalar reads. -/
theorem work_endpoint_cached [CommMonoid R] (empty : IsEmpty V)
    (fs : List (ObservedFactor V (Fin q) R)) (h : CachedState fs) :
    (endpoint empty fs).work = productWork fs := by
  rw [endpoint, Observed.work_product]
  unfold productWork factorReadWork
  congr 1
  congr 1
  apply List.map_congr_left
  intro f hf
  exact h f hf _

/-- Exact per-product address profile, including multiplicities. -/
theorem reads_productWork (fs : List (ObservedFactor V (Fin q) R)) :
    (productWork fs).reads =
      ⟨(fs.map (fun f => f.arity + 1)).sum, 0, 0, 0,
        (fs.map (fun f => f.arity)).sum, (fs.map (fun f => f.arity)).sum, fs.length⟩ := by
  have h : (factorReadWork fs).reads =
      ⟨(fs.map (fun f => f.arity + 1)).sum, 0, 0, 0,
        (fs.map (fun f => f.arity)).sum, (fs.map (fun f => f.arity)).sum, fs.length⟩ := by
    induction fs with
    | nil => rfl
    | cons f fs ih =>
        change (cachedReadWork f.arity).reads.add (factorReadWork fs).reads = _
        rw [ih]
        simp [cachedReadWork, ReadWork.add, Nat.add_comm]
  simp [productWork, Work.add, h, ReadWork.add, ReadWork.zero]

/-- One output row performs `q` actual incident-product loops. The address
components scale by `q`, independently of coefficient values. -/
theorem reads_rowWork (fs : List (ObservedFactor V (Fin q) R)) :
    (rowWork q fs).reads =
      ⟨q * (fs.map (fun f => f.arity + 1)).sum, 0, 0, 0,
        q * (fs.map (fun f => f.arity)).sum,
        q * (fs.map (fun f => f.arity)).sum, q * fs.length⟩ := by
  simp only [rowWork, Work.add, Work.scale, reads_productWork, ReadWork.add, ReadWork.zero]
  simp

end Counting.Algorithm.VariableEliminationWork
