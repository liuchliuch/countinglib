import Paper2.BellReduction.IterationEncoding
import Paper2.BellReduction.ValueIteration

/-! End-to-end occurrence normalization from the unchanged original instance
bytes. Its counter is extracted by a finite list scanner, not supplied as extra
input. The resulting graph has at most two designated Bell vertices. -/
namespace Paper2.BellReduction
open Complexity ExactInput Tractable Problem BellMachines RawTriple Bell ReedMuller
open FixedFieldMachines GraphPreprocessing BinaryCompose

noncomputable def normalize (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (G : Instance L) : Instance L :=
  ((guardedValid L hzero coreLabel hl ha)^[G.val.vertices.length]) G

/-- The unary counter is read from actual framed vertex rows. -/
noncomputable def vertexCountComputes (L : Language) :
    Computes (inputEncoding L) UnaryBinary.unaryEncoding
      (fun G => G.val.vertices.length) :=
  recode (verticesComputes.andThen (Lists.lengthUnaryComputes RawClosedNetwork.vertexEncoding))
    Subtype.val (fun _ => rfl) (fun _ => rfl)

/-- An actual polynomial-time finite machine computes normalization on original
graph bytes, without an externally supplied bound or proof-bearing input. -/
noncomputable def normalizeComputes (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8) :
    Computes (inputEncoding L) (inputEncoding L) (normalize L hzero coreLabel hl ha) :=
  (pairComputes (vertexCountComputes L) (identityComputes (inputEncoding L))).andThen
    (iterateComputes L hzero coreLabel hl ha)

theorem normalize_count (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (G : Instance L) :
    RawOccurrence.markedCount (normalize L hzero coreLabel hl ha G).val.vertices ≤ 2 := by
  unfold normalize
  rw [guardedValid_iterate_raw]
  exact iterate_at_most_two G.property hzero coreLabel hl ha

theorem normalize_value (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (c : AlgebraicComplex) (d l : Bool) (hL0 : 0 < L.count)
    (hbell : (⟨L.arity 0,L.signature ⟨0,hL0⟩⟩ : AnySignature AlgebraicComplex) =
      ⟨2,bellTable d l⟩)
    (hcore : (⟨L.arity coreLabel,L.signature ⟨coreLabel,hl⟩⟩ : AnySignature AlgebraicComplex) =
      ⟨8,fun x => c * core x⟩) (G : Instance L) :
    value .nativeX L (normalize L hzero coreLabel hl ha G) =
      (c * sign l)^roundsRemaining G * value .nativeX L G :=
  normalized_value L hzero coreLabel hl ha c d l hL0 hbell hcore G

end Paper2.BellReduction
