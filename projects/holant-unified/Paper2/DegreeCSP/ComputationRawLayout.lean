import Paper2.DegreeCSP.ComputationLayout

/-! The runtime layout operates on the literal raw payload. Promise proofs
are used only to validate the final graph. On promised inputs the total layout
is definitionally the same record list as the typed semantic layout. -/
namespace Paper2.DegreeCSP.ComputationLayout
open Holant.Complexity
open scoped BigOperators
noncomputable section

def outerOffsetRaw (r : Raw) (v : ℕ) : ℕ :=
  ∑ i : Fin r.variables,if i.val<v then Raw.degree r i.val else 0
def occurrenceCountRaw (r : Raw) : ℕ := ∑ i : Fin r.variables,Raw.degree r i.val
def innerOffsetRaw (k : ℕ) (r : Raw) (v : ℕ) : ℕ := occurrenceCountRaw r+
  ∑ i : Fin r.variables,if i.val<v then internalCount k (Raw.degree r i.val) else 0
def edgeCountRaw (k : ℕ) (r : Raw) : ℕ := occurrenceCountRaw r+
  ∑ i : Fin r.variables,internalCount k (Raw.degree r i.val)
def originalEndpointRaw (r : Raw) (p : Raw.Ports r) : RawEndpoint :=
  (outerOffsetRaw r (Raw.address r p)+(Raw.occurrences r (Raw.address r p)).idxOf p,false)
def originalRowRaw (r : Raw) (v : Fin r.factors.length) : RawVertex :=
  ((r.factors.get v).1,List.ofFn (fun j : Fin (r.factors.get v).2.length =>
    originalEndpointRaw r ⟨v,j⟩))
def variableRowsRaw (k label : ℕ) (r : Raw) (i : Fin r.variables) : List RawVertex :=
  macroRows k label (Raw.degree r i.val) (outerOffsetRaw r i.val) (innerOffsetRaw k r i.val)
def originalVerticesRaw (r : Raw) : List RawVertex :=
  (List.finRange r.factors.length).map (originalRowRaw r)
def extraVerticesRaw (k label : ℕ) (r : Raw) : List RawVertex :=
  (List.finRange r.variables).flatMap (variableRowsRaw k label r)
def verticesRaw (k label : ℕ) (r : Raw) : List RawVertex :=
  originalVerticesRaw r++extraVerticesRaw k label r
def rawTotal (k label : ℕ) (r : Raw) : RawClosedNetwork :=
  ⟨verticesRaw k label r,List.replicate (edgeCountRaw k r) 0⟩

theorem rawTotal_eq {s : ℕ} {a : ℕ → ℕ} {k : ℕ} (label : ℕ) (r : Raw.Input s a k) :
    rawTotal k label r.val=raw label r := by
  rfl

end
end Paper2.DegreeCSP.ComputationLayout
