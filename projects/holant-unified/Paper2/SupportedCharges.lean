import Paper2.ChargeBridge

/-! The gcd-height set is computed from actual nonzero entries of a finite
signature family. Zero charges may be included in the auxiliary finite set;
the theorem below proves that deleting them leaves the paper's gcd unchanged. -/
namespace Paper2.ChargeBridge
open scoped BigOperators

variable {K ι : Type} [Fintype ι] [CommRing K] [NoZeroDivisors K] [Nontrivial K]

/-- Every half-charge represented by a nonzero table entry, including charge zero. -/
noncomputable def supportedCharges (r : ι → ℕ) (f : (i : ι) → Signature K (r i)) : Finset ℤ := by
  classical
  exact Finset.univ.biUnion (fun i =>
    (Finset.univ.filter (fun x : Fin (r i) → Bool => f i x ≠ 0)).image halfCharge)

lemma mem_supportedCharges (r : ι → ℕ) (f : (i : ι) → Signature K (r i)) (c : ℤ) :
    c ∈ supportedCharges r f ↔ ∃ i, ∃ x : Fin (r i) → Bool, f i x ≠ 0 ∧ halfCharge x = c := by
  classical
  simp [supportedCharges]

lemma input_charge_divisible (r : ι → ℕ) (f : (i : ι) → Signature K (r i)) (i : ι) :
    Tensor.HalfChargeDivisible (f i) ((supportedCharges r f).gcd Int.natAbs : ℕ) := by
  intro x hx
  exact ChargeSemigroup.gcd_dvd_charge ((mem_supportedCharges r f _).mpr ⟨i, x, hx, rfl⟩)

/-- This is exactly the source gcd over *nonzero* supported half-charges. -/
lemma gcd_delete_zero (r : ι → ℕ) (f : (i : ι) → Signature K (r i)) :
    (supportedCharges r f).gcd Int.natAbs =
      ((supportedCharges r f).filter (fun c => c ≠ 0)).gcd Int.natAbs := by
  simpa only [Int.natAbs_ne_zero] using
    (supportedCharges r f).gcd_eq_gcd_filter_ne_zero (f := Int.natAbs)

/-- A selected charge retains the label of an actual input signature and an
actual supported word, so tensor copies cannot introduce a foreign signature. -/
structure Selection (r : ι → ℕ) (f : (i : ι) → Signature K (r i)) (C : Finset ℤ) where
  label : C → ι
  word : (c : C) → Fin (r (label c)) → Bool
  supported : ∀ c, f (label c) (word c) ≠ 0
  charge_eq : ∀ c, halfCharge (word c) = c.val

lemma selection_exists (r : ι → ℕ) (f : (i : ι) → Signature K (r i)) :
    Nonempty (Selection r f (supportedCharges r f)) := by
  classical
  have h : ∀ c : supportedCharges r f,
      ∃ i, ∃ x : Fin (r i) → Bool, f i x ≠ 0 ∧ halfCharge x = c.val :=
    fun c => (mem_supportedCharges r f c.val).mp c.property
  choose label x hs hc using h
  exact ⟨⟨label, x, hs, hc⟩⟩

namespace Selection
variable {r : ι → ℕ} {f : (i : ι) → Signature K (r i)} {C : Finset ℤ}

def arity (s : Selection r f C) (c : C) : ℕ := r (s.label c)
def signatures (s : Selection r f C) (c : C) : Signature K (s.arity c) := f (s.label c)
end Selection

/-- Fully instantiated arithmetic/self-loop conclusion for a finite input
family with both signs. All tensor vertices are selected from that original
family. The resulting derivations use no formal subtraction or extra signature. -/
theorem finite_family_endpoints (r : ι → ℕ) (f : (i : ι) → Signature K (r i))
    (h2 : (2 : K) ≠ 0) (heven : ∀ i, Even (r i))
    (hpos : ∃ i, ∃ x : Fin (r i) → Bool, f i x ≠ 0 ∧ 0 < halfCharge x)
    (hneg : ∃ i, ∃ x : Fin (r i) → Bool, f i x ≠ 0 ∧ halfCharge x < 0) :
    let C := supportedCharges r f
    let d := C.gcd Int.natAbs
    0 < d ∧ ∃ s : Selection r f C, ∃ np nm : C → ℕ,
      ∃ P N : Signature K (2 * d),
        EndpointSelfLoop.Reachable K (ChargeProducts.table np s.arity s.signatures) P ∧
        EndpointSelfLoop.Reachable K (ChargeProducts.table nm s.arity s.signatures) N ∧
        P (fun _ => true) ≠ 0 ∧ N (fun _ => false) ≠ 0 ∧
        Tensor.HalfChargeDivisible P d ∧ Tensor.HalfChargeDivisible N d := by
  classical
  dsimp only
  have hp : ∃ p ∈ supportedCharges r f, 0 < p := by
    obtain ⟨i, x, hx, hc⟩ := hpos
    exact ⟨halfCharge x, (mem_supportedCharges r f _).mpr ⟨i, x, hx, rfl⟩, hc⟩
  have hm : ∃ p ∈ supportedCharges r f, p < 0 := by
    obtain ⟨i, x, hx, hc⟩ := hneg
    exact ⟨halfCharge x, (mem_supportedCharges r f _).mpr ⟨i, x, hx, rfl⟩, hc⟩
  obtain ⟨s⟩ := selection_exists r f
  refine ⟨ChargeSemigroup.gcd_positive hp, s, ?_⟩
  exact endpoints_from_charge_set (supportedCharges r f) hp hm s.arity s.signatures s.word
    h2 (fun c => heven (s.label c)) s.supported s.charge_eq
    (fun c => input_charge_divisible r f (s.label c))

/-- Complete coefficient-operation branch of Lemma 4.1: starting with the
original finite signature tables, produce opposite endpoint tables by actual
tensor copies/self-loops, and then either an explicit small-connector mountain
or scalar opposite point masses. No polynomial-time reduction is asserted by
this table-level theorem. -/
theorem finite_family_mountain_or_pure_tables
    (r : ι → ℕ) (f : (i : ι) → Signature K (r i))
    (h2 : (2 : K) ≠ 0) (heven : ∀ i, Even (r i))
    (hpos : ∃ i, ∃ x : Fin (r i) → Bool, f i x ≠ 0 ∧ 0 < halfCharge x)
    (hneg : ∃ i, ∃ x : Fin (r i) → Bool, f i x ≠ 0 ∧ halfCharge x < 0) :
    let C := supportedCharges r f
    let d := C.gcd Int.natAbs
    0 < d ∧ ∃ sel : Selection r f C, ∃ np nm : C → ℕ,
      ∃ P N : Tensor K (Fin d ⊕ Fin d),
        EndpointSelfLoop.Reachable K (ChargeProducts.table np sel.arity sel.signatures) P ∧
        EndpointSelfLoop.Reachable K (ChargeProducts.table nm sel.arity sel.signatures) N ∧
        P (fun _ => true) ≠ 0 ∧ N (fun _ => false) ≠ 0 ∧
        ((∃ M, MountainConstruction.PairGadget P N M ∧
          IsMountain (Tensor.reindex (MountainConstruction.blockEquiv d) M)) ∨
          (P = MountainConstruction.onePointMass (P (fun _ => true)) ∧
            N = MountainConstruction.zeroPointMass (N (fun _ => false)))) := by
  classical
  obtain ⟨hd, sel, np, nm, P, N, hP, hN, hPend, hNend, hPd, hNd⟩ :=
    finite_family_endpoints r f h2 heven hpos hneg
  let d := (supportedCharges r f).gcd Int.natAbs
  let e := (MountainConstruction.blockEquiv d).symm
  let PB := Tensor.reindex e P
  let NB := Tensor.reindex e N
  have hPB : PB (fun _ => true) ≠ 0 := hPend
  have hNB : NB (fun _ => false) ≠ 0 := hNend
  refine ⟨hd, sel, np, nm, PB, NB,
    .trans hP (.reindex e P), .trans hN (.reindex e N), hPB, hNB, ?_⟩
  exact MountainConstruction.endpoint_pair_mountain_or_pure_of_divisible hd hPB hNB
    (Tensor.reindex_halfChargeDivisible e hPd) (Tensor.reindex_halfChargeDivisible e hNd)

end Paper2.ChargeBridge
