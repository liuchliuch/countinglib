import Paper2.BellReduction.RawNativeSemantics
import Mathlib.Data.List.Nodup

/-! Native-edge elimination. The concrete endpoint operations and local
bijection proofs are adapted from the frozen 2026-10-06 handoff's
UniversalPairReduction surgery; no theorem or object from that project is
imported. This independent module is freshly kernel checked in Paper2. -/
namespace Paper2.BellReduction.NativeSmoothing
open Complexity

def edgeEnds (offset count : ℕ) : List RawEndpoint :=
  (List.range count).flatMap fun e => [(offset+e,false),(offset+e,true)]

@[simp] theorem edgeEnds_zero (offset : ℕ) : edgeEnds offset 0 = [] := rfl

theorem edgeEnds_add (offset a b : ℕ) :
    edgeEnds offset (a+b) = edgeEnds offset a ++ edgeEnds (offset+a) b := by
  simp [edgeEnds,List.range_add,List.flatMap_append,List.flatMap_map,
    Function.comp_def,Nat.add_assoc]

theorem expectedEndpoints_eq (r : RawClosedNetwork) :
    r.expectedEndpoints = edgeEnds 0 r.edges.length := by
  unfold RawClosedNetwork.expectedEndpoints edgeEnds
  simp only [List.flatMap,Nat.zero_add]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem mem_edgeEnds (offset count : ℕ) (p : RawEndpoint) :
    p ∈ edgeEnds offset count ↔ offset ≤ p.1 ∧ p.1 < offset+count := by
  rcases p with ⟨e,bit⟩
  simp only [edgeEnds,List.mem_flatMap,List.mem_range,List.mem_cons,List.mem_nil_iff,
    or_false,Prod.mk.injEq]
  constructor
  · rintro ⟨i,hi,h|h⟩ <;> omega
  · rintro ⟨h₁,h₂⟩
    refine ⟨e-offset,by omega,?_⟩
    cases bit <;> simp <;> omega

end Paper2.BellReduction.NativeSmoothing
