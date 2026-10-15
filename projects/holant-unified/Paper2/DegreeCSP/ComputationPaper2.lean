import Paper2.DegreeCSP.Computation
import Paper2.Complexity.ClosedNetworkEncoding

/-! Reinterpret the compiler's concrete records in the independent Paper 2
record type. Every byte and every machine transition is retained literally. -/
namespace Paper2.DegreeCSP
open Computability
noncomputable section

def paper2RawRecord (r : Holant.Complexity.RawClosedNetwork) : Paper2.Complexity.RawClosedNetwork :=
  ⟨r.vertices,r.edges⟩

private theorem product_bytes {A B : Type} (ha pa : Encoding A Bool) (hb pb : Encoding B Bool)
    (heA : ∀a,ha.encode a=pa.encode a) (heB : ∀b,hb.encode b=pb.encode b) (v : A × B) :
    (Holant.Complexity.framedProductEncoding ha hb).encode v =
      (Paper2.Complexity.framedProductEncoding pa pb).encode v := by
  change Holant.Algebraic.frame (ha.encode v.1) ++ hb.encode v.2 =
    Paper2.Algebraic.frame (pa.encode v.1) ++ pb.encode v.2
  rw [heA,heB,TractableAlgorithms.Paper1Machine.frame_eq]

private theorem list_bytes {A : Type} (h p : Encoding A Bool) (he : ∀a,h.encode a=p.encode a)
    (vs : List A) :
    (Holant.Complexity.framedListEncoding h).encode vs =
      (Paper2.Complexity.framedListEncoding p).encode vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change true :: (Holant.Algebraic.frame (h.encode v) ++
      (Holant.Complexity.framedListEncoding h).encode vs) =
      true :: (Paper2.Algebraic.frame (p.encode v) ++
      (Paper2.Complexity.framedListEncoding p).encode vs)
    rw [he,TractableAlgorithms.Paper1Machine.frame_eq,ih]

private theorem endpoint_bytes (v : Holant.Complexity.RawEndpoint) :
    Holant.Complexity.RawClosedNetwork.endpointEncoding.encode v =
      Paper2.Complexity.RawClosedNetwork.endpointEncoding.encode v :=
  product_bytes _ _ _ _ (fun _=>rfl) (fun _=>rfl) v
private theorem vertex_bytes (v : Holant.Complexity.RawVertex) :
    Holant.Complexity.RawClosedNetwork.vertexEncoding.encode v =
      Paper2.Complexity.RawClosedNetwork.vertexEncoding.encode v :=
  product_bytes _ _ _ _ (fun _=>rfl) (list_bytes _ _ endpoint_bytes) v

theorem paper2RawRecord_bytes (r : Holant.Complexity.RawClosedNetwork) :
    Holant.Complexity.RawClosedNetwork.encoding.encode r =
      Paper2.Complexity.RawClosedNetwork.encoding.encode (paper2RawRecord r) :=
  product_bytes _ _ _ _ (list_bytes _ _ vertex_bytes) (list_bytes _ _ (fun _=>rfl))
    (r.vertices,r.edges)

def paper2RawQueryComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Paper2.Complexity.BinaryCompose.Computes Raw.encoding
      Paper2.Complexity.RawClosedNetwork.encoding
      (fun r=>paper2RawRecord (ComputationLayout.rawTotal k label r)) :=
  Paper2.Complexity.FixedFieldMachines.recode (rawQueryComputes k hk label) id (fun _=>rfl)
    (fun r=>paper2RawRecord_bytes _)

def promisedPaper2RawQueryComputes (s : ℕ) (a : ℕ → ℕ) (k : ℕ) (hk : 0<k) (label : ℕ) :
    Paper2.Complexity.BinaryCompose.Computes (Raw.validatedEncoding s a k)
      Paper2.Complexity.RawClosedNetwork.encoding
      (fun r=>paper2RawRecord (ComputationLayout.raw label r)) :=
  Paper2.Complexity.FixedFieldMachines.recode (promisedRawQueryComputes s a k hk label) id (fun _=>rfl)
    (fun r=>paper2RawRecord_bytes _)

end
end Paper2.DegreeCSP
