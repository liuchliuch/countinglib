import Paper2.Certificates.Q6CardComplement
import Paper2.Certificates.Q6Action

/-! Every actual S₆/global-complement orbit action preserves the complete
four-wire two-copy safety hypothesis, including the endpoint product term. -/
namespace Paper2.Certificates.Q6
open Coverage

def globalComplementAction : Action where
  ports := id
  complement := true
  coords := complementCoord

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma globalComplementAction_valid : globalComplementAction.Valid := by
  apply Action.check_sound
  decide +kernel

variable {K : Type*} [CommRing K] [NoZeroDivisors K]

lemma coefficient_complement (q : Fin 20 → K) (S : PortSet) :
    coefficient (fun i => q (complementCoord i)) (mask S) =
      coefficient q (mask (Finset.univ \ S)) := by
  have h := coefficient_action q globalComplementAction globalComplementAction_valid S
  change coefficient (fun i => q (complementCoord i)) (mask S) =
    coefficient q (mask (Finset.univ \ S.image id)) at h
  simpa only [Finset.image_id] using h

lemma AllTwoCopySafe.complement (q : Fin 20 → K) (t : K) (h : AllTwoCopySafe q t) :
    AllTwoCopySafe (fun i => q (complementCoord i)) t := by
  intro s hs
  rw [twoCopyArray_complement q _ t s hs.raw (coefficient_complement q)]
  exact (h s hs).complement

lemma AllTwoCopySafe.relabel (q q' : Fin 20 → K) (t : K)
    (h : AllTwoCopySafe q t) (p : Equiv.Perm Port)
    (hq : ∀ S : PortSet, coefficient q' (mask S) = coefficient q (mask (S.image p))) :
    AllTwoCopySafe q' t := by
  intro s hs
  rw [twoCopyArray_relabel p q q' t s hq]
  exact AllTwoCopySafe.of_raw q t h (relabelCard p s) (relabelCard_raw_valid p s hs.raw)

/-- Exact closure used when transporting the exhaustive twenty-coordinate
rows back to the original signature. The same endpoint product t is retained. -/
theorem AllTwoCopySafe.action (q : Fin 20 → K) (t : K) (h : AllTwoCopySafe q t)
    (a : Action) (ha : a.Valid) : AllTwoCopySafe (fun i => q (a.coords i)) t := by
  cases hc : a.complement
  · apply AllTwoCopySafe.relabel q _ t h (a.portEquiv ha)
    intro S
    simpa only [actSet,hc,Bool.false_eq_true,if_false] using coefficient_action q a ha S
  · apply AllTwoCopySafe.relabel (fun i => q (complementCoord i)) _ t
      (AllTwoCopySafe.complement q t h) (a.portEquiv ha)
    intro S
    rw [coefficient_complement]
    simpa only [actSet,hc,if_true] using coefficient_action q a ha S

end Paper2.Certificates.Q6
