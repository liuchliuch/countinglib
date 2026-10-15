import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine.Generators
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.Output
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.Completeness
import Holant.Proofs.Algorithms.OptionalValue
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapInterface

/-! A finite physical catalogue of certified output root descriptors.
Every proposed polynomial/certificate pair is checked by the total isolation
emitter before its descriptor enters a tuple. The tuple generator has no root
validity promise, and covers every finite list of algebraic target values. -/
namespace Paper2.ExactInput.Recognition.NativeCertifiedCatalogue
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Root := Holant.LocalDrafts.EffectiveAlgebraic.RootCode
noncomputable abbrev Values := Holant.Tractable.AlgebraicComplex
abbrev rootEncoding := CertificateMachine.rootEncoding
abbrev rootsEncoding := CommonFieldMachine.rootsEncoding
abbrev inputEncoding := pairEncoding encodingNatBool encodingNatBool
abbrev outputEncoding := framedListEncoding rootsEncoding

def pairs (height : ℕ) : List CertificateMachine.Input :=
  RootSearchDriver.cross (StructuredCatalogue.polynomials height)
    (RootSearchDriver.certificates height)

def roots (height : ℕ) : List Root :=
  (pairs height).flatMap (fun p => (CertificateMachine.emit p).toList)

def tuples (count height : ℕ) : List (List Root) :=
  StructuralListMachine.exactLength (roots height) count

theorem mem_roots_iff (c : Root) (height : ℕ) :
    c ∈ roots height ↔
      ∃ p ∈ StructuredCatalogue.polynomials height,
        ∃ t ∈ RootSearchDriver.certificates height,
          CertificateMachine.emit (p,t) = some c := by
  simp only [roots,List.mem_flatMap,Option.mem_toList]
  constructor
  · rintro ⟨⟨p,t⟩,hpt,he⟩
    obtain ⟨hp,ht⟩ := RootSearchDriver.mem_cross.mp hpt
    exact ⟨p,hp,t,ht,he⟩
  · rintro ⟨p,hp,t,ht,he⟩
    exact ⟨(p,t),RootSearchDriver.mem_cross.mpr ⟨hp,ht⟩,he⟩

theorem mem_roots_valid {height : ℕ} {c : Root} (hc : c ∈ roots height) :
    ∃ z : Values, c.Represents (z : ℂ) := by
  obtain ⟨p,_,t,_,he⟩ := (mem_roots_iff c height).mp hc
  obtain ⟨z,hz⟩ := CertificateMachine.emit_sound he
  exact ⟨⟨z,mem_algebraicClosure_iff.mpr
    (Holant.LocalDrafts.EffectiveAlgebraic.RootCode.represents_isAlgebraic hz)⟩,hz⟩

private theorem vector_entries {A : Type} (xs : List A) {n : ℕ}
    (v : Fin n → A) (hv : v ∈ FiniteBranchEnumeration.vectors xs n) :
    ∀ i, v i ∈ xs := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨a,ha,hrest⟩ := List.mem_flatMap.mp hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hrest
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ha
    · exact ih w hw j

theorem mem_tuples_iff (cs : List Root) (count height : ℕ) :
    cs ∈ tuples count height ↔ cs.length = count ∧ ∀ c ∈ cs, c ∈ roots height := by
  constructor
  · intro h
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
    refine ⟨List.length_ofFn,?_⟩
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact vector_entries (roots height) v hv i
  · rintro ⟨hlen,hc⟩
    subst count
    exact List.mem_map.mpr ⟨cs.get,
      FiniteBranchEnumeration.mem_vectors _ _ (fun i => hc _ (List.get_mem ..)),
      List.ofFn_get cs⟩

theorem tuple_length {count height : ℕ} {cs : List Root}
    (hc : cs ∈ tuples count height) : cs.length = count :=
  ((mem_tuples_iff cs count height).mp hc).1

theorem tuple_entries_valid {count height : ℕ} {cs : List Root}
    (hc : cs ∈ tuples count height) : ∀ c ∈ cs, ∃ z : Values, c.Represents (z : ℂ) := by
  intro c hmem
  exact mem_roots_valid (((mem_tuples_iff cs count height).mp hc).2 c hmem)

theorem emitted_root_covers (p : RationalPolynomialCode) (t : Certificate)
    {c : Root} (he : CertificateMachine.emit (p,t) = some c) :
    ∃ H : ℕ, ∀ height ≥ H, c ∈ roots height := by
  obtain ⟨P,hP⟩ := StructuredCatalogue.covers_polynomials p
  obtain ⟨T,hT⟩ := StructuredCatalogue.covers_certificates t
  refine ⟨max P T,?_⟩
  intro height hheight
  exact (mem_roots_iff _ _).mpr
    ⟨p,hP height ((le_max_left P T).trans hheight),
      t,hT height ((le_max_right P T).trans hheight),he⟩

theorem emitted_tuples_covers {count : ℕ}
    (p : Fin count → RationalPolynomialCode) (t : Fin count → Certificate)
    (c : Fin count → Root) (he : ∀ i, CertificateMachine.emit (p i,t i) = some (c i)) :
    ∃ H : ℕ, ∀ height ≥ H, List.ofFn c ∈ tuples count height := by
  classical
  choose H hH using fun i => emitted_root_covers (p i) (t i) (he i)
  refine ⟨Finset.univ.sup H,?_⟩
  intro height hheight
  apply (mem_tuples_iff _ _ _).mpr
  refine ⟨List.length_ofFn,?_⟩
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  exact hH i height ((Finset.le_sup (Finset.mem_univ i)).trans hheight)

/-- The returned descriptor and its eventual height are completeness witnesses,
not inputs to the physical generator below. -/
theorem roots_covers (z : Values) :
    ∃ c : Root, ∃ H : ℕ, c.Represents (z : ℂ) ∧ ∀ height ≥ H, c ∈ roots height := by
  obtain ⟨p,t,_,ht,hz,_⟩ := exists_algebraic_certificate (z : ℂ)
    (mem_algebraicClosure_iff.mp z.property) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨P,hP⟩ := StructuredCatalogue.covers_polynomials p
  obtain ⟨T,hT⟩ := StructuredCatalogue.covers_certificates t
  refine ⟨t.rootCode p,max P T,hz,?_⟩
  intro height hheight
  apply (mem_roots_iff _ _).mpr
  refine ⟨p,hP height ((le_max_left P T).trans hheight),
    t,hT height ((le_max_right P T).trans hheight),?_⟩
  simp [CertificateMachine.emit,CertificateMachine.check_eq,ht]

theorem tuples_covers_fn {count : ℕ} (z : Fin count → Values) :
    ∃ c : Fin count → Root, ∃ H : ℕ,
      (∀ i, (c i).Represents (z i : ℂ)) ∧
      ∀ height ≥ H, List.ofFn c ∈ tuples count height := by
  classical
  choose c H hc hH using fun i => roots_covers (z i)
  refine ⟨c,Finset.univ.sup H,hc,?_⟩
  intro height hheight
  apply (mem_tuples_iff _ _ _).mpr
  refine ⟨List.length_ofFn,?_⟩
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  exact hH i height ((Finset.le_sup (Finset.mem_univ i)).trans hheight)

theorem tuples_covers (z : List Values) :
    ∃ cs : List Root, ∃ H : ℕ,
      List.Forall₂ (fun c v => c.Represents (v : ℂ)) cs z ∧
      ∀ height ≥ H, cs ∈ tuples z.length height := by
  obtain ⟨c,H,hc,hH⟩ := tuples_covers_fn z.get
  refine ⟨List.ofFn c,H,?_,hH⟩
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp,?_⟩
  intro i h₁ h₂
  simpa using hc ⟨i,h₂⟩

noncomputable section

def pairsExecutes : Executes encodingNatBool
    (framedListEncoding CertificateMachine.inputEncoding) pairs :=
  NegativeCatalogueMachine.Programs.cross CertificateMachine.polynomialEncoding
    CertificateMachine.certificateEncoding NegativeCatalogueMachine.Programs.polynomials
      NegativeCatalogueMachine.Programs.certificates

/-- Only present emitter outputs become singleton lists. The optional-value
map and defaulting are existing physical tag/copy programs. -/
def presentComputes : Computes CertificateMachine.resultEncoding rootsEncoding
    (fun c : Option Root => c.toList) := by
  let w := congrComputes
    ((OriginalCoefficient.OptionMap.computes
      (NegativeCertificateMachine.Lists.singleton rootEncoding)).andThen
        (Holant.LocalDrafts.MainChain.OptionalValue.getDComputes rootsEncoding []))
    (fun c => by cases c <;> rfl)
  exact recode w id (fun c => by cases c <;> rfl) (fun c => by cases c <;> rfl)

def emitExecutes : Executes CertificateMachine.inputEncoding rootsEncoding
    (fun p => (CertificateMachine.emit p).toList) :=
  (StructuralListMachine.ofFinite CertificateMachine.emitComputes).comp
    (Executes.ofComputes presentComputes)

def rootsExecutes : Executes encodingNatBool rootsEncoding roots := by
  let cell := (Executes.ofComputes
    (Wiring.secondComputes encodingNatBool CertificateMachine.inputEncoding)).comp emitExecutes
  let mapped := NegativeCertificateMachine.Lists.map encodingNatBool CertificateMachine.inputEncoding
    rootsEncoding pairsExecutes (fun _ p => (CertificateMachine.emit p).toList) cell
  exact (mapped.comp (Executes.ofComputes (WireLists.flatten rootEncoding))).congr
    (fun height => by simp only [roots,List.flatMap_def])

/-- A single total finite-control generator for every runtime count and height.
Neither a valid root nor a stopping height is assumed in this interface. -/
def executes : Executes inputEncoding outputEncoding (fun p : ℕ × ℕ => tuples p.1 p.2) := by
  let count := Executes.ofComputes (Wiring.firstComputes encodingNatBool encodingNatBool)
  let certified := (Executes.ofComputes
    (Wiring.secondComputes encodingNatBool encodingNatBool)).comp rootsExecutes
  exact ((count.pair certified).comp (StructuralListMachine.exactExecutes rootEncoding)).congr
    (fun _ => rfl)

end
end Paper2.ExactInput.Recognition.NativeCertifiedCatalogue
