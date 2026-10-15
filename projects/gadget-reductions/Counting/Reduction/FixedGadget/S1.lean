import Counting.Reduction.FixedGadget.Basic
import Counting.Bridge.Holant
import Counting.Gadget.Composition

/-! A semantic compatibility square on the supported ordinary-port network image.
This is not a serializer for arbitrary S1 incidence or isolated S1 variables. -/
namespace Counting.Reduction.FixedGadget
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Counting.Model Counting.Gadget
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommSemiring R] {sourceCount s b : ℕ} {arity : ℕ → ℕ}

/-- Put the actual template's hidden edge ends into the S1 finite-index presentation. -/
def templatePresentation (g : Template) (hg : g.WellFormed s b arity)
    (signatures : (i : Fin s) → Holant.Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R) :
    Presentation (Bridge.Holant.adapt (g.network hg signatures kernels)).language
      (Fin g.boundary) where
  hidden := Fintype.card (Fin g.edges.length × Bool)
  inst := (Bridge.Holant.toOpenInstance (g.network hg signatures kernels)).renameHidden
    (Fintype.equivFin (Fin g.edges.length × Bool))

/-- Every boundary assignment retains its original ordered value. -/
theorem templatePresentation_table (g : Template) (hg : g.WellFormed s b arity)
    (signatures : (i : Fin s) → Holant.Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R) (a : Fin g.boundary → Bool) :
    (templatePresentation g hg signatures kernels).table a =
      (g.network hg signatures kernels).denote a := by
  exact (OpenInstance.partition_renameHidden_equiv
    (Bridge.Holant.toOpenInstance (g.network hg signatures kernels))
    (Fintype.equivFin (Fin g.edges.length × Bool)) a).trans
      (Bridge.Holant.partition_toOpenInstance _ a)

/-- Adapt the actual byte compiler's output and source to S1; their partitions agree. -/
theorem partition_compile_network
    (templates : ℕ → Template)
    (hg : ∀ i < sourceCount, (templates i).WellFormed s b arity)
    (source : (i : Fin sourceCount) → Holant.Signature R (sourceArity templates i.val))
    (signatures : (i : Fin s) → Holant.Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R)
    (hlocal : ∀ i, macroSignatures templates hg signatures kernels i = source i)
    (r : Input sourceCount b (sourceArity templates)) :
    (Bridge.Holant.toOpenInstance ((compile templates hg r).val.realize
      (compile templates hg r).property signatures kernels)).partition Fin.elim0 =
    (Bridge.Holant.toOpenInstance (r.val.realize r.property source kernels)).partition
      Fin.elim0 := by
  rw [Bridge.Holant.partition_toOpenInstance, Bridge.Holant.partition_toOpenInstance]
  exact value_compile templates hg source signatures kernels hlocal r

/-- If S1 substitution is applied to this same supported source network, its
proved result agrees with the graph compiler, for every exact S1 presentation.
This states value compatibility; it does not identify the two variable enumerations. -/
theorem substitution_alignment
    (templates : ℕ → Template)
    (hg : ∀ i < sourceCount, (templates i).WellFormed s b arity)
    (source : (i : Fin sourceCount) → Holant.Signature R (sourceArity templates i.val))
    (signatures : (i : Fin s) → Holant.Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R)
    (hlocal : ∀ i, macroSignatures templates hg signatures kernels i = source i)
    (r : Input sourceCount b (sourceArity templates))
    {ι : Type} {L : Language Bool R ι}
    (P : Substitution.Gadgets L
      (Bridge.Holant.adapt (r.val.realize r.property source kernels)).language)
    (hP : Substitution.Realizes P) :
    (Substitution.compile P
      (Bridge.Holant.toOpenInstance (r.val.realize r.property source kernels))).partition
        Fin.elim0 =
    (Bridge.Holant.toOpenInstance ((compile templates hg r).val.realize
      (compile templates hg r).property signatures kernels)).partition Fin.elim0 := by
  rw [Substitution.partition_compile P hP]
  exact (partition_compile_network templates hg source signatures kernels hlocal r).symm
end
end Counting.Reduction.FixedGadget
