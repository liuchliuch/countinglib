import Counting.Bridge.OpenNetwork.Corrected
import Counting.Bridge.Holant
import Holant.OpenNetworkComposition.OrdinaryNormalization.EmptyFree
import Holant.OpenNetworkComposition.OfOpen

/-! Degeneration to the existing S1 bridge of canonical ordinary `Holant.Network`.
The conversion and its denotation theorem are the original normalization results. -/
noncomputable section
namespace Counting.Bridge.OpenNetwork

variable {R : Type} {n : Nat}

/-- If every boundary coordinate is ordinary, a free stub cannot exist, because
its own distinguished boundary coordinate would have to be both constructors. -/
theorem noFreeOfOrdinary (N : _root_.Holant.OpenNetwork R n)
    (h : ∀ j, ∃ p, N.shape.boundary j = .inl p) : IsEmpty (Fin N.shape.free) where
  false f := by
    obtain ⟨p, hp⟩ := h (N.shape.freeBoundary f)
    rw [N.shape.free_boundary] at hp
    cases hp

variable [CommSemiring R]

/-- The actual canonical normalization, enumerated as the original Network type. -/
def ordinaryNetwork (N : _root_.Holant.OpenNetwork R n)
    (h : ∀ j, ∃ p, N.shape.boundary j = .inl p) : _root_.Holant.Network R n := by
  letI := noFreeOfOrdinary N h
  exact (_root_.Holant.OpenNetworkComposition.OrdinaryNormalization.ordinary
    (_root_.Holant.OpenNetworkComposition.FiniteNetwork.ofOpen N)).toNetwork

/-- Reuse the original normalization proof, with its full vertex and wire factors. -/
theorem denote_ordinaryNetwork (N : _root_.Holant.OpenNetwork R n)
    (h : ∀ j, ∃ p, N.shape.boundary j = .inl p) :
    (ordinaryNetwork N h).denote = N.tensor := by
  let := noFreeOfOrdinary N h
  unfold ordinaryNetwork
  rw [_root_.Holant.FiniteNetwork.denote_toNetwork,
    _root_.Holant.OpenNetworkComposition.OrdinaryNormalization.ordinary_denote,
    _root_.Holant.OpenNetworkComposition.FiniteNetwork.ofOpen_tensor]

/-- The corrected bridge agrees with the preexisting ordinary-port S1 bridge. -/
theorem partition_ordinary_tensor (N : _root_.Holant.OpenNetwork R n)
    (h : ∀ j, ∃ p, N.shape.boundary j = .inl p) (x : Fin n → Bool) :
    (toTensorInstance N).partition x =
      (Counting.Bridge.Holant.toOpenInstance (ordinaryNetwork N h)).partition x := by
  rw [partition_toTensorInstance, Counting.Bridge.Holant.partition_toOpenInstance,
    denote_ordinaryNetwork]

/-- The raw bridge agrees with the same ordinary-port S1 bridge. -/
theorem partition_ordinary_raw (N : _root_.Holant.OpenNetwork R n)
    (h : ∀ j, ∃ p, N.shape.boundary j = .inl p) (x : Fin n → Bool) :
    (toOpenInstance N).partition x =
      (Counting.Bridge.Holant.toOpenInstance (ordinaryNetwork N h)).partition x := by
  rw [← partition_tensor_eq_raw_of_ordinary N h, partition_ordinary_tensor N h]

/-- Closed networks specialize to the preexisting ordinary closed scalar bridge. -/
theorem partition_closed (N : _root_.Holant.OpenNetwork R 0) (x : Fin 0 → Bool) :
    (toOpenInstance N).partition x =
      (Counting.Bridge.Holant.toOpenInstance
        (ordinaryNetwork N (fun j => Fin.elim0 j))).partition x :=
  partition_ordinary_raw N (fun j => Fin.elim0 j) x

end Counting.Bridge.OpenNetwork
