import Paper2.HeightOne.Cyclic.CardMatching
import Paper2.HeightOne.Cyclic.ZeroPairs

/-! The cyclic actual representative menu supplies the analytic matching-card
premise by proved minimality and the exact 2c Walsh identity. No analytic
linear combination is asserted to be realizable. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable ExactInput GroupSplit GroupSplit.MatrixGroup PhaseCards EndpointSelfLoop
variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]
local instance : Fintype (rootsOfUnity N AlgebraicComplex) := Fintype.ofFinite _

/-- All roots, with a fixed actual representative each, form a finite binary
menu. The menu additionally processes both native orientations. -/
def rotationMenu (C : RotationCards F N) : BinaryMenu F where
  count := Fintype.card (rootsOfUnity N AlgebraicComplex)
  binary i := C.binary ((Fintype.equivFin (rootsOfUnity N AlgebraicComplex)).symm i)
  actual i := C.actual _

def rotationChoice (C : RotationCards F N) {n : ℕ} (f : Signature AlgebraicComplex n)
    (a b : Fin n) (hab : a ≠ b) (s : rootsOfUnity N AlgebraicComplex) :
    (rotationMenu C).Choices ⟨n, f⟩ :=
  (⟨(a, b), hab⟩, (Fintype.equivFin (rootsOfUnity N AlgebraicComplex)) s, false)

lemma rotation_produced (C : RotationCards F N) {n : ℕ} (f : Signature AlgebraicComplex n)
    (a b : Fin n) (hab : a ≠ b) (s : rootsOfUnity N AlgebraicComplex) :
    (rotationMenu C).produced ⟨n, f⟩ (rotationChoice C f a b hab s) =
      ⟨Fintype.card (Remaining a b), Tensor.reindex (Fintype.equivFin (Remaining a b))
        (C.contraction a b hab s f)⟩ := by
  simp [BinaryMenu.produced, BinaryMenu.oriented, rotationMenu, rotationChoice, RotationCards.contraction]

lemma support_smul {ι : Type} [Fintype ι] (c : AlgebraicComplex) (hc : c ≠ 0)
    (f : Tensor AlgebraicComplex ι) : support (c • f) = support f := by
  classical
  ext x
  simp [mem_support, hc]

/-- Source equality-matching support on an arbitrary remaining-port type,
using an explicit standard finite enumeration only for the external order. -/
def EqualityMatchingSupport {K : Type*} [Field K] {ι : Type} [Fintype ι] (f : Tensor K ι) : Prop :=
  ∃ P : Pairing (Fintype.card ι),
    support (Tensor.reindex (Fintype.equivFin ι) f) = equalityCode P

lemma EqualityMatchingSupport.origin {K : Type*} [Field K] {ι : Type} [Fintype ι]
    {f : Tensor K ι} (hf : EqualityMatchingSupport f) : f (fun _ => false) ≠ 0 := by
  obtain ⟨P, hP⟩ := hf
  have hm : (fun _ => false) ∈ equalityCode P := (mem_equalityCode _ _).mpr (fun _ => rfl)
  rw [← hP, mem_support] at hm
  exact hm

/-- The actual saturation/minimality data gives equality-matching support for
every nonzero analytic plus card at every root phase. -/
theorem minimum_plusCard_matching (C : RotationCards F N) (L : Language)
    (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hG : actualClasses L.family = cyclicPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n)
    (hprocessed : (rotationMenu C).Processed ⟨n, f⟩ L)
    (a b : Fin n) (hab : a ≠ b) (s : rootsOfUnity N AlgebraicComplex)
    (hn : plusContraction a b hab (s.val : AlgebraicComplex) (walshCoordinates f) ≠ 0) :
    EqualityMatchingSupport (plusContraction a b hab (s.val : AlgebraicComplex) (walshCoordinates f)) := by
  let k := rotationChoice C f a b hab s
  let g := (rotationMenu C).produced ⟨n, f⟩ k
  have hg : g = ⟨Fintype.card (Remaining a b),
      Tensor.reindex (Fintype.equivFin (Remaining a b)) (C.contraction a b hab s f)⟩ :=
    rotation_produced C f a b hab s
  have hwalsh : walshCoordinates g.2 = (2 * C.scale s) •
      Tensor.reindex (Fintype.equivFin (Remaining a b))
        (plusContraction a b hab (s.val : AlgebraicComplex) (walshCoordinates f)) := by
    simp only [g, k, BinaryMenu.produced, rotationChoice, BinaryMenu.oriented, rotationMenu,
      Bool.false_eq_true, if_false, Equiv.symm_apply_apply]
    rw [walshCoordinates_reindex]
    change Tensor.reindex (Fintype.equivFin (Remaining a b))
      (walshCoordinates (C.contraction a b hab s f)) = _
    rw [C.walsh]
    rfl
  have hgn : g.2 ≠ 0 := by
    intro hz
    rw [hz, walsh_zero] at hwalsh
    apply hn
    funext x
    have he := congrFun hwalsh (fun j => x ((Fintype.equivFin (Remaining a b)).symm j))
    have hh : (2 * C.scale s) * plusContraction a b hab (s.val : AlgebraicComplex)
        (walshCoordinates f) x = 0 := by
      simpa only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Tensor.reindex_apply,
        Equiv.symm_apply_apply] using he.symm
    exact (mul_eq_zero.mp hh).resolve_left (C.walsh_scale_ne_zero s)
  have hp : 0 < g.1 := by
    have harity := (rotationMenu C).produced_arity ⟨n, f⟩ k
    have hmin3 := hmin.ge_three
    change g.1 + 2 = n at harity
    omega
  obtain ⟨P, hP⟩ := minimum_card_walsh_matching (rotationMenu C) L heven hsafe hG hmin
    ⟨n, f⟩ rfl hprocessed k ⟨hp, hgn⟩
  refine ⟨P, ?_⟩
  rw [hwalsh, support_smul _ (C.walsh_scale_ne_zero s)] at hP
  exact hP

end
end Paper2.HeightOne.Cyclic
