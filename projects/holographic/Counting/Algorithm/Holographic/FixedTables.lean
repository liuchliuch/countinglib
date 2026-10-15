import Counting.Algorithm.Holographic.Upstream
import Holant.Proofs.Algorithms.HolographicTransport

/-!
# Fixed-table machines with the S1 partition as their specification

All language tables, the finite rational basis `F`, and the matrices `M,N` are
fixed before the input graph. The input and output encodings and the actual
length-controlled oracle machines are the frozen H1 ones. Only their semantic
specification is transported through the proved S1 bridge. This module does not
charge or implement a search for a variable basis or variable signature tables.
-/

noncomputable section

namespace Counting.Algorithm.Holographic.FixedTables

open Holant Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose

variable {K : Type} [Field K] [Algebra ℚ K] {d s b : Nat} {arity : Nat → Nat}

/-- Parse the original validated graph and expose its actual S1 kernel network. -/
def network (F : FixedField K d) (T : ExactSignatureTables d s b arity)
    (r : ExactSignatureTables.Input s b arity) : Model.KernelNetwork Bool K (Fin 0) :=
  Bridge.Holant.adapt (r.val.realize r.property
    (fun i x => F.decode (T.vertex i x)) (fun i x y => F.decode (T.edge i x y)))

/-- Evaluation specified by the public occurrence-list partition, on the
original validated graph encoding and the original field output encoding. -/
def value (F : FixedField K d) (T : ExactSignatureTables d s b arity)
    (r : ExactSignatureTables.Input s b arity) : K :=
  (network F T r).toOpenInstance.partition Fin.elim0

/-- The parser, actual network, and S1 occurrence expansion agree exactly. -/
theorem value_eq (F : FixedField K d) (T : ExactSignatureTables d s b arity) :
    value F T = T.evaluate F := by
  funext r
  rw [value, Model.KernelNetwork.partition_toOpenInstance]
  exact (T.evaluate_eq_decoded F r).symm

/-- The old table-construction procedure realizes precisely the public transform. -/
theorem network_tables (F : FixedField K d) (T : ExactSignatureTables d s b arity)
    (M N : Kernel Bool K) (r : ExactSignatureTables.Input s b arity) :
    network F (LocalDrafts.MainChain.HolographicTransport.tables F T M N) r =
      transform (network F T r) M N := by
  unfold network transform Bridge.Holant.adapt Bridge.Holant.adaptShape
  simp only [LocalDrafts.MainChain.HolographicTransport.tables,
    LinearEquiv.apply_symm_apply, RawClosedNetwork.realize]
  rfl

/-- Fixed-table semantic invariance now has the common S1 partition specification. -/
theorem transformed_value (F : FixedField K d) (T : ExactSignatureTables d s b arity)
    (M N : Kernel Bool K) (hMN : M * N = 1) :
    value F (LocalDrafts.MainChain.HolographicTransport.tables F T M N) = value F T := by
  rw [value_eq, value_eq]
  exact funext (LocalDrafts.MainChain.HolographicTransport.value_eq F T M N hMN)

/-- The existing real one-query machine, with query/reply length bounds retained. -/
def toTransformed (F : FixedField K d) (T : ExactSignatureTables d s b arity)
    (M N : Kernel Bool K) (hMN : M * N = 1) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (value F T) (value F (LocalDrafts.MainChain.HolographicTransport.tables F T M N)) := by
  simpa only [value_eq] using
    LocalDrafts.MainChain.HolographicTransport.toTransformed F T M N hMN

/-- The reverse real one-query machine uses the same original graph encoding. -/
def fromTransformed (F : FixedField K d) (T : ExactSignatureTables d s b arity)
    (M N : Kernel Bool K) (hMN : M * N = 1) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (value F (LocalDrafts.MainChain.HolographicTransport.tables F T M N)) (value F T) := by
  simpa only [value_eq] using
    LocalDrafts.MainChain.HolographicTransport.fromTransformed F T M N hMN

/-- Transport an implemented target evaluator. The caller must supply its actual
`Computes` machine and polynomial transition certificate. -/
def computes (F : FixedField K d) (T : ExactSignatureTables d s b arity)
    (M N : Kernel Bool K) (hMN : M * N = 1)
    (a : Computes (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (value F (LocalDrafts.MainChain.HolographicTransport.tables F T M N))) :
    Computes (RawClosedNetwork.validatedEncoding s b arity) F.encoding (value F T) := by
  rw [value_eq] at a ⊢
  exact LocalDrafts.MainChain.HolographicTransport.computes F T M N hMN a

end Counting.Algorithm.Holographic.FixedTables
