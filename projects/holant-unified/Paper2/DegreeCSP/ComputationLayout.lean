import Paper2.DegreeCSP.RawData
import Holant.Complexity.ClosedNetworkEncoding

/-! Literal record layout for the degree-k incidence compiler. Original
constraints retain row and port order. Occurrence edges are grouped by declared
variable and stable occurrence ordinal. Variable equality macros have their
main rows first, followed by the two connector rows for each consecutive pair.
An unused variable retains its two-copy closed macro of value two. -/
namespace Paper2.DegreeCSP.ComputationLayout
open Holant.Complexity Holant.Complexity.RawClosedNetwork
open scoped BigOperators
noncomputable section
variable {s : ℕ} {a : ℕ → ℕ} {k : ℕ}

def multiplicity (k d : ℕ) : ℕ := d/k
def internalCount (k d : ℕ) : ℕ := if d=0 then k else (multiplicity k d-1)*k
def vertexCount (k d : ℕ) : ℕ := if d=0 then 2 else 3*multiplicity k d-2

def outerOffset (r : Raw.Input s a k) (v : ℕ) : ℕ :=
  ∑ i : Fin r.val.variables,if i.val<v then Raw.degree r.val i.val else 0

def occurrenceCount (r : Raw.Input s a k) : ℕ :=
  ∑ i : Fin r.val.variables,Raw.degree r.val i.val

def innerOffset (r : Raw.Input s a k) (v : ℕ) : ℕ := occurrenceCount r+
  ∑ i : Fin r.val.variables,if i.val<v then internalCount k (Raw.degree r.val i.val) else 0

def edgeCount (r : Raw.Input s a k) : ℕ := occurrenceCount r+
  ∑ i : Fin r.val.variables,internalCount k (Raw.degree r.val i.val)

def originalEndpoint (r : Raw.Input s a k) (p : Raw.Ports r.val) : RawEndpoint :=
  (outerOffset r (Raw.address r.val p)+(Raw.grouping r p).2.val,false)

def originalRow (r : Raw.Input s a k) (v : Fin r.val.factors.length) : RawVertex :=
  ((r.val.factors.get v).1,
    List.ofFn (fun j : Fin (r.val.factors.get v).2.length => originalEndpoint r ⟨v,j⟩))

def mainEndpoint (k m outer inner t j : ℕ) : RawEndpoint :=
  if j=0 ∧ 0<t then (inner+(t-1)*k+1,false) else
  if j=1 ∧ t+1<m then (inner+t*k,false) else (outer+t*k+j,true)

def firstConnectorEndpoint (k outer inner t j : ℕ) : RawEndpoint :=
  if j=0 then (outer+t*k+1,true) else
  if j=1 then (outer+(t+1)*k,true) else (inner+t*k+j,false)

def secondConnectorEndpoint (k inner t j : ℕ) : RawEndpoint := (inner+t*k+j,true)

def macroRows (k label d outer inner : ℕ) : List RawVertex :=
  if d=0 then
    [ (label,List.ofFn (fun j : Fin k => (inner+j.val,false))),
      (label,List.ofFn (fun j : Fin k => (inner+j.val,true))) ]
  else
    (List.finRange (multiplicity k d)).map (fun t =>
      (label,List.ofFn (fun j : Fin k =>
        mainEndpoint k (multiplicity k d) outer inner t.val j.val))) ++
    (List.finRange (multiplicity k d-1)).flatMap (fun t =>
      [ (label,List.ofFn (fun j : Fin k => firstConnectorEndpoint k outer inner t.val j.val)),
        (label,List.ofFn (fun j : Fin k => secondConnectorEndpoint k inner t.val j.val)) ])

def variableRows (label : ℕ) (r : Raw.Input s a k) (i : Fin r.val.variables) : List RawVertex :=
  macroRows k label (Raw.degree r.val i.val) (outerOffset r i.val) (innerOffset r i.val)

def originalVertices (r : Raw.Input s a k) : List RawVertex :=
  (List.finRange r.val.factors.length).map (originalRow r)

def extraVertices (label : ℕ) (r : Raw.Input s a k) : List RawVertex :=
  (List.finRange r.val.variables).flatMap (variableRows label r)

def vertices (label : ℕ) (r : Raw.Input s a k) : List RawVertex :=
  originalVertices r++extraVertices label r

def raw (label : ℕ) (r : Raw.Input s a k) : RawClosedNetwork :=
  ⟨vertices label r,List.replicate (edgeCount r) 0⟩

end
end Paper2.DegreeCSP.ComputationLayout
