import Paper2.Certificates.Q8AtlasMatchingBridge
import Paper2.Certificates.Q8TranslationDeck

/-! Stable source-level interface between the complete matching atlas and
actual endpoint-preserving X-contraction decks. -/
namespace Paper2.Certificates.Q8.Atlas

open CommonPhase

/-- The original named pair, with its fixed ascending endpoint order. -/
def portPair (d : PairIndex) : PortPair Port :=
  ⟨(deleted d).1,(deleted d).2,deleted_distinct d⟩

/-- Keep the actual mate map of each actual source X-matching product. -/
def indexedMatching
    (P : (e : PortPair Port) → XMatching (EndpointSelfLoop.Remaining e.first e.second))
    (d : PairIndex) : Matching d := Matching.fromXMatching d (P (portPair d))

/-- Pull a tensor back from original port names to the displayed F₂³ labels. -/
def labeledTensor {K : Type*} (p : Equiv.Perm Port) (F : Signature K 8) : Signature K 8 :=
  fun x => F (fun v => x (p v))

def TranslationAt (p q : Port) (x : ReedMuller.Word) : Prop :=
  ∀ v, v ≠ p → v ≠ q → x (Fin.xor v (Fin.xor p q)) = !(x v)

instance (p q : Port) (x : ReedMuller.Word) : Decidable (TranslationAt p q x) :=
  inferInstanceAs (Decidable (∀ v, v ≠ p → v ≠ q → x (Fin.xor v (Fin.xor p q)) = !(x v)))

end Paper2.Certificates.Q8.Atlas
