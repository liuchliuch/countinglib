import Counting.Bridge.OpenNetwork.Canonical

/-! A client that composes actual canonical realizations twice, preserving the
fixed supplied family and edge kind without going through an S1 adapter. -/
open Holant
example {K : Type} [CommSemiring K] {a b c : Nat}
    (family : SignatureFamily K) (W : EdgeKind)
    (f : Signature K a) (g : Signature K b) (h : Signature K c)
    (hf : Gadget.Realizes family W f) (hg : Gadget.Realizes family W g)
    (hh : Gadget.Realizes family W h) :
    Gadget.Realizes family W (Signature.tensor (Signature.tensor f g) h) :=
  OpenNetworkComposition.realizes_tensor family W _ h
    (OpenNetworkComposition.realizes_tensor family W f g hf hg) hh
