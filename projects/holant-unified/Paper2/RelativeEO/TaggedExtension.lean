import Paper2.ExactInput.Computation.IndexedLanguage
import Paper2.ExactInput.Coverage
import Paper2.Problem

/-! One distinguished added signature gets its own literal label zero. Existing
labels are shifted, even if their denotation equals the added table. Thus an
occurrence promise counts designated vertices, not semantic equality of tables. -/
set_option backward.isDefEq.respectTransparency false

namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation
open Paper2.Complexity Paper2.Problem Computability

noncomputable def tagged (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n) : Language :=
  ⟨codeOf g :: L.val, by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact codeOf_valid _
    · exact L.property c hc⟩

@[simp] theorem tagged_count (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n) :
    (tagged L g).count = L.count + 1 := rfl

@[simp] theorem tagged_arity_zero (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n) :
    (tagged L g).arity 0 = n := rfl

@[simp] theorem tagged_arity_succ (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (i : ℕ) : (tagged L g).arity (i + 1) = L.arity i := rfl

@[simp] theorem tagged_zero (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n) :
    (⟨(tagged L g).arity 0, (tagged L g).signature ⟨0, by simp⟩⟩ :
      AnySignature AlgebraicComplex) = ⟨n, g⟩ := by
  apply ((tagged L g).member_as_code ⟨0, by rw [tagged_count]; omega⟩).trans
  change (⟨n, (codeOf g).denote (codeOf_valid g)⟩ : AnySignature AlgebraicComplex) = _
  rw [codeOf_denote]

@[simp] theorem tagged_succ (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (i : Fin L.count) :
    (⟨(tagged L g).arity i.succ.val, (tagged L g).signature i.succ⟩ :
      AnySignature AlgebraicComplex) = ⟨L.arity i.val, L.signature i⟩ := by
  rw [(tagged L g).member_as_code, L.member_as_code]
  rfl

@[simp] theorem tagged_family (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n) :
    (tagged L g).family = insert (⟨n, g⟩ : AnySignature AlgebraicComplex) L.family := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl (tagged_zero L g)
    · exact Or.inr ⟨j, (tagged_succ L g j).symm⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨⟨0, by rw [tagged_count]; omega⟩, tagged_zero L g⟩
    · exact ⟨i.succ, tagged_succ L g i⟩

/-- Computable count on the actual serialized graph, preserving duplicate table
labels and every nullary vertex. Zero is the fresh distinguished label. -/
def occurrenceCount (r : RawClosedNetwork) : ℕ :=
  (r.vertices.filter (fun v => v.1 == 0)).length

abbrev TaggedInstance (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (p : ℕ → Prop) := {G : Instance (tagged L g) // p (occurrenceCount G.val)}

/-- A decidable occurrence promise adds no input bits. Decoding checks the real
raw graph first and then the executable number-of-designated-occurrences test. -/
noncomputable def taggedEncoding (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (p : ℕ → Prop) [DecidablePred p] : Encoding (TaggedInstance L g p) Bool where
  encode G := (inputEncoding (tagged L g)).encode G.val
  decode bits := ((inputEncoding (tagged L g)).decode bits).bind
    (fun G => if h : p (occurrenceCount G.val) then some ⟨G, h⟩ else none)
  decode_encode G := by simp [G.property]

@[simp] theorem taggedEncoding_bytes (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (p : ℕ → Prop) [DecidablePred p] (G : TaggedInstance L g p) :
    (taggedEncoding L g p).encode G = RawClosedNetwork.encoding.encode G.val.val := rfl

end Paper2.RelativeEO
