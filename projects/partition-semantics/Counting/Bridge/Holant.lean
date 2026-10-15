import Counting.Model.Holant
import Counting.Upstream.HolantNetwork

/-!
# Bridge from the original Holant ordinary-port network

`Counting.Upstream.HolantNetwork` preserves the declarations and proofs of
`Holant/Network.lean` at holant-dichotomy-lean commit
`97731bce1618bef0d9ee7911b6ac8bc8698077b2`. Its two original dependencies are also
preserved, with only import paths changed. Exact source and target hashes are
recorded in `provenance/Holant/source-checks.json`.

This adapter imports the actual original declarations. Its value theorem covers
`Holant.Network.denote`, which has ordinary boundary ports and general edge
kernels. It does not cover `Holant.OpenNetwork.raw` or its separately corrected
boundary tensor; those have paired free stubs and different semantics.
-/

namespace Counting.Bridge.Holant

variable {R : Type} {n : Nat}

/-- Copy the original port bijection, without identifying the ends of an edge. -/
def adaptShape (s : _root_.Holant.NetworkShape n) : Model.KernelNetworkShape (Fin n) where
  vertices := s.vertices
  arity := s.arity
  edges := s.edges
  ports := s.ports

/-- The original Boolean network with the same vertex tables and edge kernels. -/
def adapt (N : _root_.Holant.Network R n) : Model.KernelNetwork Bool R (Fin n) where
  shape := adaptShape N.shape
  vertex := N.vertex
  edge := N.edge

/-- The adapted raw signature is the actual original network denotation. -/
theorem raw_adapt [CommSemiring R] (N : _root_.Holant.Network R n) :
    (adapt N).raw = N.denote := rfl

/-- Expand the original network into explicit vertex and edge constraints. -/
def toOpenInstance (N : _root_.Holant.Network R n) :
    Model.OpenInstance (adapt N).language (Fin n) (Fin N.shape.edges × Bool) :=
  (adapt N).toOpenInstance

/-- The CSP partition table equals the original upstream denotation, for every
ordered boundary assignment and every supplied general binary edge kernel. -/
theorem partition_toOpenInstance [CommSemiring R] (N : _root_.Holant.Network R n)
    (x : Fin n → Bool) :
    (toOpenInstance N).partition x = N.denote x :=
  Model.KernelNetwork.partition_toOpenInstance (adapt N) x

end Counting.Bridge.Holant
