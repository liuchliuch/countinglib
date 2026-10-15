import Paper2.SupportedCharges
import Paper2.NetworkRealization
import Paper2.NetworkSubstitution

/-!
The concrete graph-construction part of Lemma 4.1. Starting with only the
original finite input labels, actual finite native-X networks realize either
a mountain of gcd height or both nonzero scalar point masses of that arity.
Obtaining *unary* pins from the second case requires the separately identified
Paper 1 factor-extraction reduction; it is not asserted as a direct gadget.
-/
namespace Paper2.ChargeBridge
open scoped BigOperators

variable {K ι : Type} [Fintype ι] [CommRing K] [NoZeroDivisors K] [Nontrivial K]

def inputFamily (r : ι → ℕ) (f : (i : ι) → Signature K (r i)) : SignatureFamily K :=
  Set.range (fun i => (⟨r i, f i⟩ : AnySignature K))

/-- A scaled literal all-equal point mass on the ordered original ports. -/
def pointMass (b : Bool) (n : ℕ) (c : K) : Signature K n :=
  fun x => if x = (fun _ => b) then c else 0

lemma reindex_eq_const_iff {α β : Type*} (e : α ≃ β) (x : β → Bool) (b : Bool) :
    (fun i => x (e i)) = (fun _ => b) ↔ x = (fun _ => b) := by
  constructor
  · intro h
    funext j
    have := congrFun h (e.symm j)
    simpa using this
  · rintro rfl
    rfl

lemma reindex_onePointMass (d : ℕ) (c : K) :
    Tensor.reindex (MountainConstruction.blockEquiv d) (MountainConstruction.onePointMass c) =
      pointMass true (2 * d) c := by
  funext x
  simp only [Tensor.reindex, MountainConstruction.onePointMass, pointMass,
    reindex_eq_const_iff]

lemma reindex_zeroPointMass (d : ℕ) (c : K) :
    Tensor.reindex (MountainConstruction.blockEquiv d) (MountainConstruction.zeroPointMass c) =
      pointMass false (2 * d) c := by
  funext x
  simp only [Tensor.reindex, MountainConstruction.zeroPointMass, pointMass,
    reindex_eq_const_iff]

/-- The full finite-family construction produces genuine resource-labelled
networks, with every tensor copy, loop, coordinate permutation, and multi-copy
connector compiled into the original graph model. -/
theorem finite_family_mountain_or_point_mass_networks
    (r : ι → ℕ) (f : (i : ι) → Signature K (r i))
    (h2 : (2 : K) ≠ 0) (heven : ∀ i, Even (r i))
    (hpos : ∃ i, ∃ x : Fin (r i) → Bool, f i x ≠ 0 ∧ 0 < halfCharge x)
    (hneg : ∃ i, ∃ x : Fin (r i) → Bool, f i x ≠ 0 ∧ halfCharge x < 0) :
    let d := (supportedCharges r f).gcd Int.natAbs
    0 < d ∧
      ((∃ M : Signature K (2 * d), IsMountain M ∧
          ∃ G : Network K (2 * d), G.Uses (inputFamily r f) ∧ G.NativeX ∧ G.denote = M) ∨
        ∃ p q : K, p ≠ 0 ∧ q ≠ 0 ∧
          (∃ G : Network K (2 * d), G.Uses (inputFamily r f) ∧ G.NativeX ∧
            G.denote = pointMass true (2 * d) p) ∧
          (∃ G : Network K (2 * d), G.Uses (inputFamily r f) ∧ G.NativeX ∧
            G.denote = pointMass false (2 * d) q)) := by
  classical
  obtain ⟨hd, sel, np, nm, P, N, hP, hN, hPend, hNend, hout⟩ :=
    finite_family_mountain_or_pure_tables r f h2 heven hpos hneg
  have hlabels : ∀ c, (⟨sel.arity c, sel.signatures c⟩ : AnySignature K) ∈ inputFamily r f :=
    fun c => ⟨sel.label c, rfl⟩
  have hPR : NetworkRealizable (inputFamily r f) P :=
    NetworkRealizable.reachable hP (NetworkRealizable.copies np sel.arity sel.signatures hlabels)
  have hNR : NetworkRealizable (inputFamily r f) N :=
    NetworkRealizable.reachable hN (NetworkRealizable.copies nm sel.arity sel.signatures hlabels)
  refine ⟨hd, ?_⟩
  rcases hout with ⟨M, hm, hmountain⟩ | ⟨hPpure, hNpure⟩
  · exact Or.inl ⟨_, hmountain,
      ((hm.networkRealizable hPR hNR).reindex (MountainConstruction.blockEquiv _)).ordered⟩
  · refine Or.inr ⟨P (fun _ => true), N (fun _ => false), hPend, hNend, ?_, ?_⟩
    · have hR := hPR.reindex (MountainConstruction.blockEquiv _)
      rw [hPpure, reindex_onePointMass] at hR
      exact hR.ordered
    · have hR := hNR.reindex (MountainConstruction.blockEquiv _)
      rw [hNpure, reindex_zeroPointMass] at hR
      exact hR.ordered

end Paper2.ChargeBridge
