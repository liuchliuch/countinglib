import Paper2.HeightOne.PhaseCards.OrientedCards
import Paper2.HeightOne.PhaseCards.SaturationCore
import Paper2.HeightOne.Cyclic.ActualDeck

/-! Explicit finite actual xor cards and exact inclusion of finite menus. The
binary representatives used by the analytic deck are the same representatives
processed by the finite graph saturation. -/
namespace Paper2.HeightOne.PhaseCards
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Tractable ExactInput GroupSplit GroupSplit.MatrixGroup EndpointSelfLoop

namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex}

def append (M Q : BinaryMenu F) : BinaryMenu F where
  count := M.count + Q.count
  binary := Fin.addCases M.binary Q.binary
  actual := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa only [Fin.addCases_left] using M.actual i
    | right i => simpa only [Fin.addCases_right] using Q.actual i

def leftChoice (M Q : BinaryMenu F) (f : AnySignature AlgebraicComplex)
    (k : M.Choices f) : (M.append Q).Choices f :=
  (k.1, k.2.1.castAdd Q.count, k.2.2)

def rightChoice (M Q : BinaryMenu F) (f : AnySignature AlgebraicComplex)
    (k : Q.Choices f) : (M.append Q).Choices f :=
  (k.1, Fin.natAdd M.count k.2.1, k.2.2)

lemma produced_left (M Q : BinaryMenu F) (f : AnySignature AlgebraicComplex)
    (k : M.Choices f) : (M.append Q).produced f (M.leftChoice Q f k) = M.produced f k := by
  simp only [produced, leftChoice, oriented, append, Fin.addCases_left]

lemma produced_right (M Q : BinaryMenu F) (f : AnySignature AlgebraicComplex)
    (k : Q.Choices f) : (M.append Q).produced f (M.rightChoice Q f k) = Q.produced f k := by
  simp only [produced, rightChoice, oriented, append, Fin.addCases_right]

lemma Processed.left (M Q : BinaryMenu F) {f : AnySignature AlgebraicComplex} {L : Language}
    (h : (M.append Q).Processed f L) : M.Processed f L := by
  refine ⟨h.1, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
    apply h.2.1
    apply Set.mem_iUnion.mpr
    exact ⟨M.leftChoice Q f k, by simpa only [produced_left] using hk⟩
  · intro k hp hn
    have hp' : 0 < ((M.append Q).produced f (M.leftChoice Q f k)).1 := by
      simpa only [produced_left] using hp
    have hn' : ((M.append Q).produced f (M.leftChoice Q f k)).2 ≠ 0 := by
      simpa only [produced, leftChoice, oriented, append, Fin.addCases_left] using hn
    simpa only [produced_left] using h.2.2 (M.leftChoice Q f k) hp' hn'

lemma Processed.right (M Q : BinaryMenu F) {f : AnySignature AlgebraicComplex} {L : Language}
    (h : (M.append Q).Processed f L) : Q.Processed f L := by
  refine ⟨h.1, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
    apply h.2.1
    apply Set.mem_iUnion.mpr
    exact ⟨M.rightChoice Q f k, by simpa only [produced_right] using hk⟩
  · intro k hp hn
    have hp' : 0 < ((M.append Q).produced f (M.rightChoice Q f k)).1 := by
      simpa only [produced_right] using hp
    have hn' : ((M.append Q).produced f (M.rightChoice Q f k)).2 ≠ 0 := by
      simpa only [produced, rightChoice, oriented, append, Fin.addCases_right] using hn
    simpa only [produced_right] using h.2.2 (M.rightChoice Q f k) hp' hn'

end BinaryMenu

structure XorCards (F : SignatureFamily AlgebraicComplex) (N : ℕ) where
  binary : Bool → Bool → rootsOfUnity N AlgebraicComplex → AMat
  scale : Bool → Bool → rootsOfUnity N AlgebraicComplex → AlgebraicComplex
  actual : ∀ u v s, ActualNonsingular F (binary u v s)
  scale_ne_zero : ∀ u v s, scale u v s ≠ 0
  analysis_eq : ∀ u v s,
    analysisKernel (binary u v s) = scale u v s • xorKernel u v s.val

theorem xorCards_nonempty {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hN : 0 < N) (hG : actualClasses F = dihedralPhaseClasses N) : Nonempty (XorCards F N) := by
  have h : ∀ u v : Bool, ∀ s : rootsOfUnity N AlgebraicComplex,
      ∃ (B : AMat) (c : AlgebraicComplex), ActualNonsingular F B ∧ c ≠ 0 ∧
        analysisKernel B = c • xorKernel u v s.val := by
    intro u v s
    exact actual_xor_card hN hG u v s.val
      (congrArg (fun z : AlgebraicComplexˣ => (z : AlgebraicComplex))
        ((mem_rootsOfUnity N s.val).mp s.property))
  choose B c hB hc he using h
  exact ⟨⟨B, c, hB, hc, he⟩⟩

variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]
local instance : Fintype (rootsOfUnity N AlgebraicComplex) := Fintype.ofFinite _

def xorMenu (C : XorCards F N) : BinaryMenu F where
  count := Fintype.card (Bool × Bool × rootsOfUnity N AlgebraicComplex)
  binary i :=
    let q := (Fintype.equivFin (Bool × Bool × rootsOfUnity N AlgebraicComplex)).symm i
    C.binary q.1 q.2.1 q.2.2
  actual i := C.actual _ _ _

def xorChoice (C : XorCards F N) {n : ℕ} (f : Signature AlgebraicComplex n)
    (a b : Fin n) (hab : a ≠ b) (u v : Bool) (s : rootsOfUnity N AlgebraicComplex) :
    (xorMenu C).Choices ⟨n, f⟩ :=
  (⟨(a, b), hab⟩,
    (Fintype.equivFin (Bool × Bool × rootsOfUnity N AlgebraicComplex)) (u, v, s), false)

lemma xor_produced (C : XorCards F N) {n : ℕ} (f : Signature AlgebraicComplex n)
    (a b : Fin n) (hab : a ≠ b) (u v : Bool) (s : rootsOfUnity N AlgebraicComplex) :
    (xorMenu C).produced ⟨n, f⟩ (xorChoice C f a b hab u v s) =
      ⟨Fintype.card (Remaining a b), Tensor.reindex (Fintype.equivFin (Remaining a b))
        (card (nativeKernel (C.binary u v s)) a b hab f)⟩ := by
  simp [BinaryMenu.produced, BinaryMenu.oriented, xorMenu, xorChoice]

lemma xor_produced_walsh (C : XorCards F N) {n : ℕ} (f : Signature AlgebraicComplex n)
    (a b : Fin n) (hab : a ≠ b) (u v : Bool) (s : rootsOfUnity N AlgebraicComplex) :
    walshCoordinates ((xorMenu C).produced ⟨n, f⟩ (xorChoice C f a b hab u v s)).2 =
      C.scale u v s • Tensor.reindex (Fintype.equivFin (Remaining a b))
        (card (xorKernel u v s.val) a b hab (walshCoordinates f)) := by
  simp only [BinaryMenu.produced, BinaryMenu.oriented, xorMenu, xorChoice,
    Bool.false_eq_true, if_false, Equiv.symm_apply_apply]
  rw [walshCoordinates_reindex, walshCoordinates_card]
  change Tensor.reindex (Fintype.equivFin (Remaining a b))
    (card (analysisKernel (C.binary u v s)) a b hab (walshCoordinates f)) = _
  rw [C.analysis_eq]
  unfold card
  rw [contractKernel_scale]
  rfl

end
end Paper2.HeightOne.PhaseCards

