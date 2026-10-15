import Paper2.Bell
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

/-!
RM(1,3) in the manuscript's lexicographic order 000,001,...,111.
The external Boolean tensor interface is exactly `Signature K 8`.
Finite checks below use Lean's kernel reduction, never `native_decide`.
-/
namespace Paper2.ReedMuller

abbrev Parameters := Fin 4 → Bool
abbrev Word := Fin 8 → Bool

/-- Coordinates in F₂³, with most significant coordinate first. -/
def point : Fin 8 → Fin 3 → Bool :=
  ![![false, false, false], ![false, false, true],
    ![false, true, false], ![false, true, true],
    ![true, false, false], ![true, false, true],
    ![true, true, false], ![true, true, true]]

/-- Evaluation of a + u₁t₁ + u₂t₂ + u₃t₃ over F₂. -/
def affineWord (a : Parameters) : Word := fun t =>
  Bool.xor (a 0) (Bool.xor (a 1 && point t 0)
    (Bool.xor (a 2 && point t 1) (a 3 && point t 2)))

def IsCodeword (x : Word) : Prop := ∃ a : Parameters, affineWord a = x

instance (x : Word) : Decidable (IsCodeword x) := inferInstanceAs
  (Decidable (∃ a : Parameters, affineWord a = x))

/-- The actual finite set of affine truth tables. -/
def code : Finset Word := Finset.univ.image affineWord

theorem mem_code (x : Word) : x ∈ code ↔ IsCodeword x := by
  simp [code, IsCodeword]

def weight (x : Word) : ℕ := ∑ t : Fin 8, (x t).toNat

def IsCentral (x : Word) : Prop := IsCodeword x ∧ weight x = 4

instance (x : Word) : Decidable (IsCentral x) := inferInstanceAs
  (Decidable (IsCodeword x ∧ weight x = 4))

/-- The full sixteen-word signature, not merely its central layer. -/
def core {K : Type*} [Zero K] [One K] : Signature K 8 :=
  fun x => if IsCodeword x then 1 else 0

def central {K : Type*} [Zero K] [One K] : Signature K 8 :=
  fun x => if IsCentral x then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Distinct affine functions have distinct eight-coordinate truth tables. -/
theorem affineWord_injective : Function.Injective affineWord := by
  decide +kernel

/-- There are exactly sixteen codewords. -/
theorem card_code : code.card = 16 := by
  rw [code, Finset.card_image_of_injective _ affineWord_injective]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every affine word has weight zero, four, or eight. -/
theorem affineWord_weight (a : Parameters) :
    weight (affineWord a) = 0 ∨ weight (affineWord a) = 4 ∨
      weight (affineWord a) = 8 := by
  revert a
  decide +kernel

theorem codeword_weight (x : Word) (hx : IsCodeword x) :
    weight x = 0 ∨ weight x = 4 ∨ weight x = 8 := by
  obtain ⟨a, rfl⟩ := hx
  exact affineWord_weight a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The central layer has exactly fourteen words. -/
theorem card_central : (code.filter (fun x => weight x = 4)).card = 14 := by
  decide +kernel

/-- XOR of the labels of the selected coordinates, represented bitwise. -/
def supportXor (x : Word) : Fin 3 → Bool := fun j =>
  (List.ofFn (fun t : Fin 8 => x t && point t j)).foldr Bool.xor false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The central RM words are exactly the four-subsets with label XOR zero. -/
theorem central_iff_plane (x : Word) :
    IsCentral x ↔ weight x = 4 ∧ supportXor x = fun _ => false := by
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Both complementary four-point sets used in Q8.25 are information sets. -/
theorem information_sets (a b : Parameters) :
    ((∀ i : Fin 4, affineWord a (![0, 4, 2, 1] i) = affineWord b (![0, 4, 2, 1] i)) → a = b) ∧
    ((∀ i : Fin 4, affineWord a (![3, 5, 6, 7] i) = affineWord b (![3, 5, 6, 7] i)) → a = b) := by
  revert a b
  decide +kernel


/-- Product of three identically labelled Bell factors on the ordered pairs
(0,1), (2,3), (4,5) of the six surviving ports. -/
def bellTriple {K : Type*} [Ring K] (d l : Bool) : Signature K 6 :=
  fun x => Bell.ordered d l (x 0) (x 1) *
    Bell.ordered d l (x 2) (x 3) * Bell.ordered d l (x 4) (x 5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The Bell occurrence identity, first proved over integers by kernel reduction.
Deleting ports 000,001 leaves exactly the ordered pairs 010/011,100/101,110/111. -/
theorem contract_core_bell_int (d l : Bool) (x : Fin 6 → Bool) :
    Signature.contract (Bell.ordered (K := ℤ) d l) core x = bellTriple d l x := by
  revert d l x
  decide +kernel

theorem cast_core {K : Type*} [Ring K] (x : Word) :
    ((core (K := ℤ) x : ℤ) : K) = core x := by
  by_cases hx : IsCodeword x <;> simp [core, hx]

theorem cast_bell {K : Type*} [Ring K] (d l u v : Bool) :
    ((Bell.ordered (K := ℤ) d l u v : ℤ) : K) = Bell.ordered d l u v := by
  cases d <;> cases l <;> cases u <;> cases v <;>
    simp [Bell.ordered, Bell.sign]

/-- The actual tensor identity over every coefficient ring, including ℂ.
Its proof transports the kernel-checked integer identity through the integer
cast ring homomorphism; no solver answer or runtime assertion is trusted. -/
theorem contract_core_bell {K : Type*} [Ring K] (d l : Bool) :
    Signature.contract (Bell.ordered (K := K) d l) core = bellTriple d l := by
  funext x
  have h := congrArg (fun z : ℤ => (z : K)) (contract_core_bell_int d l x)
  simpa only [Signature.contract, bellTriple, Int.cast_sum, Int.cast_mul,
    cast_bell, cast_core] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The central layer has the same native-X derivative as the full core. -/
theorem contract_central_x_int (x : Fin 6 → Bool) :
    Signature.contract (Bell.X (K := ℤ)) central x = bellTriple true false x := by
  revert x
  decide +kernel

theorem cast_central {K : Type*} [Ring K] (x : Word) :
    ((central (K := ℤ) x : ℤ) : K) = central x := by
  by_cases hx : IsCentral x <;> simp [central, hx]

theorem contract_central_x {K : Type*} [Ring K] :
    Signature.contract (Bell.X (K := K)) central = bellTriple true false := by
  funext x
  have h := congrArg (fun z : ℤ => (z : K)) (contract_central_x_int x)
  simpa only [Signature.contract, bellTriple, Bell.X, Int.cast_sum, Int.cast_mul,
    cast_bell, cast_central] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The four-element subsets split into fourteen planes and fifty-six nonplanes. -/
theorem card_nonplanes :
    ((Finset.univ : Finset Word).filter (fun x =>
      weight x = 4 ∧ supportXor x ≠ fun _ => false)).card = 56 := by
  decide +kernel

end Paper2.ReedMuller
