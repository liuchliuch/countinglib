import Paper2.Paper1ProvedOracleAdapters
import Holant.Proofs.Reductions.ControlledCap
import Holant.Proofs.Reductions.CanonicalFamily.Scalars
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence

/-! The actual Paper 1 replacement compiler with every fixed gadget's scalar
retained. Its single query and context correction execute the proved finite
Boolean machines; query length is controlled for every executed prefix. -/
noncomputable section
namespace Paper2.Paper1Proved.GadgetController
open Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K]
variable {d m s : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d) (templates : ℕ → Template)
variable (hg : ∀ i < m, (templates i).WellFormed s 1 arity)
variable (T : ExactSignatureTables d s 1 arity)
variable (source : (i : Fin m) → Holant.Signature (Fin d → ℚ) (sourceArity templates i.val))
variable (c : Fin m → K) (hc : ∀ i, c i ≠ 0)

 theorem product (r : ExactSignatureTables.Input m 1 (sourceArity templates)) :
    (∏ v, c (r.val.signatureLabel r.property v)) =
      RootPreprocessing.OccurrenceProduct.value c r.val := by
  rw [← List.prod_ofFn]
  unfold RootPreprocessing.OccurrenceProduct.value
  have hh : List.ofFn (fun v : Fin r.val.vertices.length => c (r.val.signatureLabel r.property v)) =
      r.val.vertices.map (fun row => RootPreprocessing.OccurrenceProduct.total c row.1) := by
    rw [← List.ofFn_getElem_eq_map]
    apply congrArg List.ofFn
    funext v
    have hi : r.val.vertices[v.val].1 < m := (r.property.1 v).1
    simp only [RawClosedNetwork.signatureLabel,RootPreprocessing.OccurrenceProduct.total,
      List.get_eq_getElem,dif_pos hi]
  rw [hh]

 def correction : Computes (pairEncoding F.encoding F.encoding) F.encoding
    (fun p : K × K => p.1 * p.2⁻¹) :=
  (pairComputes (Wiring.firstComputes F.encoding F.encoding)
    ((Wiring.secondComputes F.encoding F.encoding).andThen (fieldInverseComputes F))).andThen
      (Concrete.fieldMultiplication F)

 def controlled
    (hd : ∀ i : Fin m,
      ((templates i.val).network (hg i.val i.isLt)
        (fun j x => F.decode (T.vertex j x))
        (fun j u v => F.decode (T.edge j u v))).denote =
          c i • (fun x => F.decode (source i x))) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding m 1 (sourceArity templates)) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      ((sourceTables templates T source).evaluate F) (T.evaluate F) := by
  let pre := pairComputes
    (Compiler.computes m 1 (sourceArity templates) templates s arity (compilerHypotheses templates hg))
    (RootPreprocessing.OccurrenceProduct.computes F c)
  apply ControlledCap.controlledContextOfEq pre (correction F) (T.outputBound F)
    ((sourceTables templates T source).evaluate F)
  intro r
  have hp := replacement_partition templates r.val r.property hg
    (fun i x => F.decode (source i x)) (fun j x => F.decode (T.vertex j x))
    (fun j u v => F.decode (T.edge j u v)) c hd
  change T.evaluate F (Compiler.value m 1 (sourceArity templates) templates s arity
      (compilerHypotheses templates hg) r) =
    (∏ v, c (r.val.signatureLabel r.property v)) * (sourceTables templates T source).evaluate F r at hp
  rw [product templates c r] at hp
  change (sourceTables templates T source).evaluate F r =
    T.evaluate F (Compiler.value m 1 (sourceArity templates) templates s arity
      (compilerHypotheses templates hg) r) * (RootPreprocessing.OccurrenceProduct.value c r.val)⁻¹
  rw [hp,mul_comm (RootPreprocessing.OccurrenceProduct.value c r.val),mul_assoc,
    mul_inv_cancel₀ (CanonicalFamily.OP.nonzero c hc r),mul_one]

end Paper2.Paper1Proved.GadgetController
