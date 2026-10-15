import Paper2.Complexity.BellMachines.RawPairingCompile
import Paper2.Complexity.BellMachines.RawSmoothingCompile
import Paper2.BellReduction.RawSmoothingBridge
import Paper2.BellReduction.RawClosures

/-! Two actual smoothing calls after each fixed reconnection, preserving both
closed-circle bits. The program equality with the semantic closure is proved
on validated input, not assumed for arbitrary malformed raw records. -/
namespace Paper2.Complexity.BellMachines.RawClosures
open Computability BinaryCompose FixedFieldMachines
open Paper2.BellReduction NativeSmoothing
noncomputable section

 def close (mode : Fin 3) (G : RawClosedNetwork) : BellReduction.RawClosures.Result :=
  let a := RawSmoothing.compile (BellReduction.RawPairing.query mode G)
  let b := RawSmoothing.compile a.query
  ⟨b.query,a.circle,b.circle⟩

 def resultEncoding : Encoding BellReduction.RawClosures.Result Bool where
  encode r := (pairEncoding RawClosedNetwork.encoding
    (pairEncoding encodingBoolBool encodingBoolBool)).encode (r.query,r.firstCircle,r.secondCircle)
  decode bits := ((pairEncoding RawClosedNetwork.encoding
    (pairEncoding encodingBoolBool encodingBoolBool)).decode bits).map
      (fun p => ⟨p.1,p.2.1,p.2.2⟩)
  decode_encode r := by
    change Option.map _ ((pairEncoding RawClosedNetwork.encoding
      (pairEncoding encodingBoolBool encodingBoolBool)).decode
      ((pairEncoding RawClosedNetwork.encoding (pairEncoding encodingBoolBool encodingBoolBool)).encode
        (r.query,r.firstCircle,r.secondCircle))) = some r
    rw [Encoding.decode_encode]
    rfl

 def smoothingQuery : Computes RawSmoothing.resultEncoding RawClosedNetwork.encoding Smoothing.Result.query :=
  recode (Wiring.firstComputes RawClosedNetwork.encoding encodingBoolBool)
    (fun r => (r.query,r.circle)) (fun _ => rfl) (fun _ => rfl)
 def smoothingCircle : Computes RawSmoothing.resultEncoding encodingBoolBool Smoothing.Result.circle :=
  recode (Wiring.secondComputes RawClosedNetwork.encoding encodingBoolBool)
    (fun r => (r.query,r.circle)) (fun _ => rfl) (fun _ => rfl)

 def computes (mode : Fin 3) : Computes RawClosedNetwork.encoding resultEncoding (close mode) := by
  let a := (RawPairing.computes mode).andThen RawSmoothing.computes
  let b := (a.andThen smoothingQuery).andThen RawSmoothing.computes
  exact recode (pairComputes (b.andThen smoothingQuery)
    (pairComputes (a.andThen smoothingCircle) (b.andThen smoothingCircle)))
    id (fun _ => rfl) (fun _ => rfl)

 def queryComputes : Computes resultEncoding RawClosedNetwork.encoding BellReduction.RawClosures.Result.query :=
  recode (Wiring.firstComputes RawClosedNetwork.encoding (pairEncoding encodingBoolBool encodingBoolBool))
    (fun r => (r.query,r.firstCircle,r.secondCircle)) (fun _ => rfl) (fun _ => rfl)

 def flagsComputes : Computes resultEncoding (pairEncoding encodingBoolBool encodingBoolBool)
    (fun r => (r.firstCircle,r.secondCircle)) :=
  recode (Wiring.secondComputes RawClosedNetwork.encoding (pairEncoding encodingBoolBool encodingBoolBool))
    (fun r => (r.query,r.firstCircle,r.secondCircle)) (fun _ => rfl) (fun _ => rfl)

 theorem eq_close {G : RawClosedNetwork} {s : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s 1 arity) (hzero : arity 0 = 2)
    (hc : 2 ≤ RawOccurrence.markedCount G.vertices) (mode : Fin 3) :
    close mode G = BellReduction.RawClosures.close mode G := by
  have hw := BellReduction.RawPairing.query_wellFormed hG hzero hc mode
  unfold close BellReduction.RawClosures.close
  rw [rawSmoothing_eq_compile hw hzero]
  dsimp only
  rw [rawSmoothing_eq_compile (NativeSmoothing.Surgery.compile_wellFormed _ hw 0 hzero) hzero]

end
end Paper2.Complexity.BellMachines.RawClosures
