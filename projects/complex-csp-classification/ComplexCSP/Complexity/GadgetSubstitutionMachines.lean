import ComplexCSP.Complexity.GadgetSubstitutionCode
import PlanarHom.ListFlattenMachines
import PlanarHom.ListDecompositionMachines
import PlanarHom.UnaryPolynomialMachines
import PlanarHom.UnaryNatConversionMachine

/-! # Actual finite-control machines for arbitrary-arity gadget attachment

The construction specializes and extends the existing checked fixed-network
machine combinators to CSP's arbitrary ordered-scope constraint codec. Fixed
gadget data is in finite control; no runtime field arithmetic is needed.
-/
namespace ComplexCSP.ComplexityGadgetSubstitution
open ComplexityCSPCode PlanarHom PlanarHom.Complexity
open PairProjectionMachines ArithmeticCircuitPrimitives BinaryArithmetic

private theorem fp_getD_fixed (v : ℕ) :
    FP BitEncoding.nat.list BitEncoding.nat (fun ps => ps.getD v 0) := by
  induction v with
  | zero => exact (ListDecompositionMachines.fp_headD _ 0).congr (fun xs => by cases xs <;> rfl)
  | succ v ih =>
    exact ((ListDecompositionMachines.fp_tail _ 0).comp ih).congr (fun xs => by cases xs <;> rfl)

private theorem fp_fixed_map {A X Y : Type} (ex : BitEncoding X) (ey : BitEncoding Y)
    (xs : List A) (f : X → A → Y) (hf : ∀ a ∈ xs, FP ex ey (fun x => f x a)) :
    FP ex ey.list (fun x => xs.map (f x)) := by
  induction xs with
  | nil => exact fp_const _ _ []
  | cons a as ih =>
    exact ((hf a (by simp)).pair (ih (fun b hb => hf b (by simp [hb])))).comp
      (ListMutationMachines.fp_cons ey)

theorem fp_remapVertex (t : Template) (v : ℕ) :
    FP (BitEncoding.unaryNat.prod BitEncoding.nat.list) BitEncoding.nat
      (fun p => remapVertex t p.1 p.2 v) := by
  by_cases hv : v < t.boundary
  · exact ((fp_snd _ _).comp (fp_getD_fixed v)).congr (fun p => by simp [remapVertex,hv])
  · have ho := (fp_fst BitEncoding.unaryNat BitEncoding.nat.list).comp
      UnaryNatConversionMachine.fp_conversion
    exact ((ho.pair (fp_const _ _ (v-t.boundary))).comp fp_addition).congr
      (fun p => by simp [remapVertex,hv])

theorem fp_vertices : FP encoding BitEncoding.unaryNat Code.vertices := by
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  exact hv.comp (fp_fst _ _)

theorem fp_constraints : FP encoding constraintEncoding.list Code.constraints := by
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  exact hv.comp (fp_snd _ _)

theorem fp_attachTemplate (t : Template) :
    FP (encoding.prod BitEncoding.nat.list) encoding
      (fun p => attachTemplate t p.1 p.2) := by
  let input := encoding.prod BitEncoding.nat.list
  have hg := fp_fst encoding BitEncoding.nat.list
  have hp := fp_snd encoding BitEncoding.nat.list
  have hv := hg.comp fp_vertices
  have hctx := hv.pair hp
  have hr (v : ℕ) := hctx.comp (fp_remapVertex t v)
  have hc (c : Gate) : FP input constraintEncoding
      (fun p => remapConstraint t p.1.vertices p.2 c) :=
    (fp_const input BitEncoding.nat c.1).pair
      (fp_fixed_map input BitEncoding.nat c.2
        (fun p v => remapVertex t p.1.vertices p.2 v) (fun v _ => hr v))
  have hconstraints := ((hg.comp fp_constraints).pair
    (fp_fixed_map input constraintEncoding t.constraints
      (fun p c => remapConstraint t p.1.vertices p.2 c) (fun c _ => hc c))).comp
        (ListMutationMachines.fp_append constraintEncoding)
  have hvertices := (hv.pair (fp_const input BitEncoding.unaryNat t.privateCount)).comp
    UnaryPolynomialMachines.fp_add
  exact (hvertices.pair hconstraints).transportOutput (fun _ => rfl)

theorem compileStep_nil (g : Code) (a : Gate) : compileStep [] g a = g := by
  cases g
  simp [compileStep,gateTemplate,attachTemplate,emptyTemplate]

theorem compileStep_cons (t : Template) (ts : List Template) (g : Code) (a : Gate) :
    compileStep (t::ts) g a =
      if a.1 = 0 then attachTemplate t g a.2 else compileStep ts g (a.1-1,a.2) := by
  rcases a with ⟨i,ps⟩
  cases i <;> simp [compileStep,gateTemplate]

theorem fp_compileStep (ts : List Template) :
    FP (encoding.prod constraintEncoding) encoding (fun p => compileStep ts p.1 p.2) := by
  let input := encoding.prod constraintEncoding
  have hg := fp_fst encoding constraintEncoding
  have ha := fp_snd encoding constraintEncoding
  have hi := ha.comp (fp_fst BitEncoding.nat BitEncoding.nat.list)
  have hp := ha.comp (fp_snd BitEncoding.nat BitEncoding.nat.list)
  induction ts with
  | nil => exact hg.congr (fun p => (compileStep_nil p.1 p.2).symm)
  | cons t ts ih =>
    have hzero := hi.comp RationalCircuits.fp_nat_isZero
    have hattach := (hg.pair hp).comp (fp_attachTemplate t)
    have hdec := (hi.pair (fp_const input BitEncoding.nat 1)).comp fp_subtraction
    have htail := (hg.pair (hdec.pair hp)).comp ih
    exact (hzero.ite hattach htail).congr (fun p => (compileStep_cons t ts p.1 p.2).symm)

end ComplexCSP.ComplexityGadgetSubstitution
