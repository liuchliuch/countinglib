import ComplexCSP.Instances.Basic
import PlanarHom.RuntimePolynomialEvaluationMachines
import PlanarHom.ListUnaryLengthMachine
import PlanarHom.FixedAlphabetOutputBounds

set_option backward.isDefEq.respectTransparency false

/-!
# Bit-coded arbitrary-arity CSP instances

Variable count is unary; symbols and ordered scope indices are binary. Lists
retain multiplicity and repeated scope positions. Validity is a separate exact
predicate. Total raw evaluation treats a malformed constraint as the unit, and
the partition promise below will restrict to valid canonical codes.
-/
namespace ComplexCSP.ComplexityCSPCode
open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines

structure Code where
  vertices : ℕ
  constraints : List (ℕ × List ℕ)
  deriving DecidableEq

def constraintEncoding : BitEncoding (ℕ × List ℕ) := BitEncoding.nat.prod BitEncoding.nat.list

def encoding : BitEncoding Code :=
  (BitEncoding.unaryNat.prod constraintEncoding.list).retract
    (fun g => (g.vertices, g.constraints)) (fun p => ⟨p.1, p.2⟩)
    (by intro g; cases g; rfl)

variable {D K : Type} {s : ℕ} (L : Language D K (Fin s))

def ConstraintValid (n : ℕ) (c : ℕ × List ℕ) : Prop :=
  ∃ h : c.1 < s, c.2.length = L.arity ⟨c.1, h⟩ ∧ ∀ v ∈ c.2, v < n

instance (n : ℕ) (c : ℕ × List ℕ) : Decidable (ConstraintValid L n c) := by
  unfold ConstraintValid
  infer_instance

def Valid (g : Code) : Prop := ∀ c ∈ g.constraints, ConstraintValid L g.vertices c
instance (g : Code) : Decidable (Valid L g) := by unfold Valid; infer_instance

/-- Actual ordered scope of a validated row; every occurrence is retained. -/
def scope (g : Code) (c : ℕ × List ℕ) (hc : ConstraintValid L g.vertices c) :
    Fin (L.arity ⟨c.1, hc.choose⟩) → Fin g.vertices := fun i =>
  ⟨c.2[i.val]'(lt_of_lt_of_eq i.isLt hc.choose_spec.1.symm),
    hc.choose_spec.2 _ (List.getElem_mem _)⟩

/-- Literal finite-instance semantics, with no boundary variables. -/
def toInstance (g : Code) (hg : Valid L g) : Instance L (Fin 0) (Fin g.vertices) :=
  ⟨g.constraints.attach.map (fun c =>
    ⟨⟨c.val.1, (hg c.val c.property).choose⟩,
      fun i => Sum.inr (scope L g c.val (hg c.val c.property) i)⟩)⟩

/-- The fixed optional entry alphabet includes the total invalid-row default. -/
abbrev Entry := Option ((i : Fin s) × (Fin (L.arity i) → D))
def entryValue [One K] : Entry L → K
  | none => 1
  | some i => L.value i.1 i.2

def constraintEntry (g : Code) (σ : Fin g.vertices → D) (c : ℕ × List ℕ) : Entry L :=
  if hc : ConstraintValid L g.vertices c then
    some ⟨⟨c.1, hc.choose⟩, σ ∘ scope L g c hc⟩
  else none

def assignmentWord (g : Code) (σ : Fin g.vertices → D) : List (Entry L) :=
  g.constraints.map (constraintEntry L g σ)

def eval [CommMonoid K] (g : Code) (σ : Fin g.vertices → D) : K :=
  ((assignmentWord L g σ).map (entryValue L)).prod

def partition [Fintype D] [CommSemiring K] (g : Code) : K := ∑ σ, eval L g σ

/-- Natural COUNT output, keeping zero-weight assignments. -/
def countAt [Fintype D] [CommMonoid K] [DecidableEq K] (g : Code) (z : K) : ℕ :=
  (Finset.univ.filter (fun σ => eval L g σ = z)).card

@[simp] theorem assignmentWord_length (g : Code) (σ : Fin g.vertices → D) :
    (assignmentWord L g σ).length = g.constraints.length := by simp [assignmentWord]

/-- Same-variable repetition, including the zeroth query and isolated variables. -/
def repeatCode (g : Code) (q : ℕ) : Code :=
  ⟨g.vertices, (List.replicate q g.constraints).flatten⟩

@[simp] theorem repeat_vertices (g : Code) (q : ℕ) : (repeatCode g q).vertices = g.vertices := rfl
@[simp] theorem repeat_length (g : Code) (q : ℕ) :
    (repeatCode g q).constraints.length = q * g.constraints.length := by
  simp [repeatCode, List.length_flatten]

theorem repeat_valid (g : Code) (hg : Valid L g) (q : ℕ) : Valid L (repeatCode g q) := by
  intro c hc
  rcases List.mem_flatten.mp hc with ⟨cs, hcs, hc⟩
  have he : cs = g.constraints := (List.mem_replicate.mp hcs).2
  subst cs
  exact hg c hc

theorem repeat_eval [CommMonoid K] (g : Code) (q : ℕ) (σ : Fin g.vertices → D) :
    eval L (repeatCode g q) σ = eval L g σ ^ q := by
  simp only [eval, assignmentWord, repeatCode, List.map_flatten, List.map_replicate,
    List.prod_flatten, List.map_map, List.prod_replicate]
  rfl

theorem repeat_partition [Fintype D] [CommSemiring K] (g : Code) (q : ℕ) :
    partition L (repeatCode g q) = ∑ σ, eval L g σ ^ q := by
  simp only [partition, repeat_eval]
  rfl

@[simp] theorem zeroth_partition [Fintype D] [CommSemiring K] (g : Code) :
    partition L (repeatCode g 0) = (Fintype.card D ^ g.vertices : ℕ) := by
  simp [repeat_partition]

/-- Unary size and explicit occurrence list control semantic instance size. -/
theorem size_le_encoding_length (g : Code) :
    g.vertices + g.constraints.length ≤ (encoding.encode g).length := by
  have h := constraintEncoding.list_length_le g.constraints
  change g.vertices + g.constraints.length ≤
    ((BitEncoding.unaryNat.prod constraintEncoding.list).encode (g.vertices, g.constraints)).length
  simp only [BitEncoding.prod_length, BitEncoding.unaryNat_length]
  omega

/-- Actual machine copying the original variable count and all scope words.
The repetition exponent is unary, matching the materialized output size. -/
theorem fp_repeat : FP (BitEncoding.unaryNat.prod encoding) encoding
    (fun p : ℕ × Code => repeatCode p.2 p.1) := by
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices, g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hq := fp_fst BitEncoding.unaryNat encoding
  have hg := fp_snd BitEncoding.unaryNat encoding
  have hn := (hg.comp hv).comp (fp_fst BitEncoding.unaryNat constraintEncoding.list)
  have hc := (hg.comp hv).comp (fp_snd BitEncoding.unaryNat constraintEncoding.list)
  have hr := ((hq.pair hc).comp (RuntimePolynomialEvaluationMachines.fp_replicate constraintEncoding.list)).comp
    (ListFlattenMachines.fp_flatten constraintEncoding)
  exact (hn.pair hr).transportOutput (fun _ => rfl)

theorem eval_toInstance [CommMonoid K] (g : Code) (hg : Valid L g)
    (σ : Fin g.vertices → D) :
    (toInstance L g hg).eval (Fin.elim0) σ = eval L g σ := by
  simp only [Instance.eval, toInstance, List.map_map, eval, assignmentWord]
  have he : (g.constraints.attach.map fun c =>
      L.value ⟨c.val.1, (hg c.val c.property).choose⟩
        (σ ∘ scope L g c.val (hg c.val c.property))) =
      g.constraints.map (fun c => entryValue L (constraintEntry L g σ c)) := by
    calc
      _ = g.constraints.attach.map (fun c => entryValue L (constraintEntry L g σ c.val)) := by
        apply List.map_congr_left
        intro c _
        simp [constraintEntry, hg c.val c.property, entryValue]
      _ = _ := List.attach_map_val (l := g.constraints)
        (f := fun c => entryValue L (constraintEntry L g σ c))
  exact congrArg List.prod he

theorem partition_toInstance [Fintype D] [CommSemiring K] (g : Code) (hg : Valid L g) :
    (toInstance L g hg).partition Fin.elim0 = partition L g := by
  simp only [Instance.partition, partition, eval_toInstance]

section OutputSize
variable [Fintype D] [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- The exponentially large mathematical assignment sum has a polynomially
bounded exact output word. This does not compute the sum in polynomial time. -/
theorem exists_partition_output_bound : ∃ p : Polynomial ℕ, ∀ g : Code,
    ((numberFieldEncoding basis).encode (partition L g)).length ≤
      p.eval (encoding.encode g).length := by
  classical
  obtain ⟨p, hp⟩ := FixedAlphabetOutputBounds.exists_output_polynomial basis
    (entryValue L) (max 1 (Fintype.card D))
  refine ⟨p, fun g => ?_⟩
  let word := fun σ : Fin g.vertices → D =>
    List.replicate g.vertices (none : Entry L) ++ assignmentWord L g σ
  have hlen : ∀ σ, (word σ).length = g.vertices + g.constraints.length := by
    intro σ
    simp [word]
  have hcard : Fintype.card (Fin g.vertices → D) ≤
      max 1 (Fintype.card D) ^ ((g.vertices + g.constraints.length) + 1) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    apply (Nat.pow_le_pow_left (Nat.le_max_right 1 _) _).trans
    exact Nat.pow_le_pow_right (Nat.le_max_left 1 _) (by omega)
  have he : (∑ σ, ((word σ).map (entryValue L)).prod) = partition L g := by
    simp [word, entryValue, partition, eval]
  rw [← he]
  exact (hp word _ hlen hcard).trans
    (MachineComposition.natPolynomial_monotone p (size_le_encoding_length g))
end OutputSize

end ComplexCSP.ComplexityCSPCode
