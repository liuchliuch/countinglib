import Paper2.Paper1ProvedOddUnaryResidual
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinFactors

/-! Two independent actual ordinary unaries physically isolate every retained
prime tensor factor. The complementary caps are selected by a checked finite
multilinear basis argument; a mathematical factor is never treated as a label. -/
namespace Paper2.Paper1Proved.OddUnary.CapBasis
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
namespace B
export GlobalCloseCompletionUnaryBothPinFactors (graph factorGraph output)
end B
namespace F
export GlobalCloseCompletionUnaryFactorCaps (lastCap order)
end F
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {K : Type} [Field K]
variable (P : Bool → Holant.Signature K 1)

def evaluate (P : Bool → Holant.Signature K 1) : (m : ℕ) → (Fin m → Bool) → Holant.Signature K m → K
  | 0, _, g => g Fin.elim0
  | m+1, y, g => evaluate P m (fun i => y i.castSucc)
      (fun z => P (y (Fin.last m)) (fun _ => false) * g (Fin.snoc z false) +
        P (y (Fin.last m)) (fun _ => true) * g (Fin.snoc z true))

def determinant : K :=
  P false (fun _ => false)*P true (fun _ => true) -
  P false (fun _ => true)*P true (fun _ => false)

include P in
theorem evaluate_complete (hd : determinant P ≠ 0) :
    ∀ m (g : Holant.Signature K m), (∀ y, evaluate P m y g = 0) → g = 0 := by
  intro m
  induction m with
  | zero =>
    intro g h
    funext x
    have hx : x = Fin.elim0 := funext fun i => Fin.elim0 i
    rw [hx]
    exact h Fin.elim0
  | succ m ih =>
    intro g h
    have hz (v : Bool) :
        (fun z : Fin m → Bool => P v (fun _ => false)*g (Fin.snoc z false) +
          P v (fun _ => true)*g (Fin.snoc z true)) = 0 := by
      apply ih
      intro y
      simpa only [evaluate,Fin.snoc_castSucc,Fin.snoc_last] using h (Fin.snoc y v)
    funext x
    let z : Fin m → Bool := fun i => x i.castSucc
    have hs : Fin.snoc z (x (Fin.last m)) = x := by
      funext i
      exact Fin.lastCases (by rw [Fin.snoc_last]) (fun j => by simp only [Fin.snoc_castSucc];rfl) i
    have h0 : P false (fun _ => false)*g (Fin.snoc z false) +
        P false (fun _ => true)*g (Fin.snoc z true) = 0 := by simpa using congrFun (hz false) z
    have h1 : P true (fun _ => false)*g (Fin.snoc z false) +
        P true (fun _ => true)*g (Fin.snoc z true) = 0 := by simpa using congrFun (hz true) z
    have e0 : determinant P * g (Fin.snoc z false) = 0 := by
      unfold determinant
      linear_combination P true (fun _ => true) * h0 - P false (fun _ => true) * h1
    have e1 : determinant P * g (Fin.snoc z true) = 0 := by
      unfold determinant
      linear_combination P false (fun _ => false) * h1 - P true (fun _ => false) * h0
    rw [← hs]
    cases x (Fin.last m)
    · exact (mul_eq_zero.mp e0).resolve_left hd
    · exact (mul_eq_zero.mp e1).resolve_left hd

theorem exists_evaluate_nonzero (hd : determinant P ≠ 0) {m : ℕ}
    (g : Holant.Signature K m) (hg : g ≠ 0) : ∃ y, evaluate P m y g ≠ 0 := by
  classical
  by_contra none
  push Not at none
  exact hg (evaluate_complete P hd m g none)

theorem last_value (U : Holant.Network K 1) {n : ℕ} (N : Holant.Network K (n+1)) (x : Fin n → Bool) :
    (F.lastCap U N).denote x =
      U.denote (fun _ => false)*N.denote (Fin.snoc x false) +
      U.denote (fun _ => true)*N.denote (Fin.snoc x true) := by
  rw [F.lastCap,capHead_denote,reboundary_denote,reboundary_denote]
  rw [← Fin.snoc_eq_cons_rotate,← Fin.snoc_eq_cons_rotate]

theorem snoc_left {n m : ℕ} (w : Fin (n+m) → Bool) (v : Bool) :
    (fun i : Fin n => (Fin.snoc w v : Fin (n+m+1) → Bool) (Fin.castAdd (m+1) i)) =
      (fun i => w (Fin.castAdd m i)) := by
  funext i
  change (Fin.snoc w v : Fin (n+m+1) → Bool) (Fin.castSucc (Fin.castAdd m i)) = _
  rw [Fin.snoc_castSucc]

theorem snoc_right {n m : ℕ} (w : Fin (n+m) → Bool) (v : Bool) :
    (fun i : Fin (m+1) => (Fin.snoc w v : Fin (n+m+1) → Bool) (Fin.natAdd n i)) =
      Fin.snoc (fun i => w (Fin.natAdd n i)) v := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.natAdd_last,Fin.snoc_last,Fin.snoc_last]
  · rw [Fin.natAdd_castSucc,Fin.snoc_castSucc,Fin.snoc_castSucc]

variable (Q : Bool → Holant.Network K 1)

theorem factor_value (n m : ℕ) (y : Fin m → Bool) (N : Holant.Network K (n+m))
    (f : Holant.Signature K n) (g : Holant.Signature K m) (c : K)
    (form : N.denote = fun w => c * f (fun i => w (Fin.castAdd m i)) *
      g (fun i => w (Fin.natAdd n i))) (x : Fin n → Bool) :
    (B.graph Q n m y N).denote x =
      c * evaluate (fun v => (Q v).denote) m y g * f x := by
  induction m with
  | zero =>
    rw [B.graph,form]
    dsimp only
    have he : (fun i : Fin 0 => x (Fin.natAdd n i)) = Fin.elim0 :=
      funext fun i => Fin.elim0 i
    simp only [evaluate,Fin.castAdd_zero,Fin.cast_eq_self,he]
    ring
  | succ m ih =>
    rw [B.graph]
    let d : Holant.Signature K m := fun z =>
      (Q (y (Fin.last m))).denote (fun _ => false)*g (Fin.snoc z false) +
      (Q (y (Fin.last m))).denote (fun _ => true)*g (Fin.snoc z true)
    have newForm : (F.lastCap (Q (y (Fin.last m))) N).denote =
        fun w => c * f (fun i => w (Fin.castAdd m i)) *
          d (fun i => w (Fin.natAdd n i)) := by
      funext w
      rw [last_value,form]
      dsimp only
      rw [snoc_left,snoc_right,snoc_left,snoc_right]
      dsimp only [d]
      ring
    rw [ih _ _ d newForm]
    rfl

variable {r n : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin r) → Holant.Signature K (a i.val))
variable (caps : Bool → NoXOrdinaryGraphAdjoin.Output H 1)
variable (N : NoXOrdinaryGraphAdjoin.Output H n)
variable {f g : Holant.AnySignature K} (s : ProperSplit (⟨n,N.network.denote⟩ : Holant.AnySignature K) f g)

theorem denote (y : Fin g.1 → Bool) :
    (B.output H caps N s y).network.denote =
      fun x => (s.scale : K)*evaluate (fun v => (caps v).network.denote) g.1 y g.2*f.2 x := by
  funext x
  change (B.factorGraph H caps N s y).denote x = _
  unfold B.factorGraph
  apply factor_value
  funext w
  rw [reboundary_denote]
  have eqn := congrFun s.equation (fun i => w (F.order H N s i))
  dsimp only at eqn
  rw [eqn]
  have hl : (fun i => w (F.order H N s (s.ports (.inl i)))) =
      (fun i => w (Fin.castAdd g.1 i)) := by
    funext i
    simp [F.order]
  have hr : (fun i => w (F.order H N s (s.ports (.inr i)))) =
      (fun i => w (Fin.natAdd f.1 i)) := by
    funext i
    simp [F.order]
  rw [hl,hr]
  ring

theorem exists_leaf (hd : determinant (fun v => (caps v).network.denote) ≠ 0)
    (nonzero : N.network.denote ≠ 0)
    (t : FactorTree (⟨n,N.network.denote⟩ : Holant.AnySignature K))
    (leaf : Holant.AnySignature K) (member : leaf ∈ t.leaves) :
    ∃ V : NoXOrdinaryGraphAdjoin.Output H leaf.1,
      Prime (⟨leaf.1,V.network.denote⟩ : Holant.AnySignature K) ∧
      ∃ c : K, c ≠ 0 ∧ V.network.denote = fun x => c*leaf.2 x := by
  have hp := FactorTree.leaves_prime t leaf member
  rcases t.leaf_split leaf member with equal | ⟨b,⟨split⟩⟩
  · subst leaf
    exact ⟨N,hp,1,one_ne_zero,by simp⟩
  · obtain ⟨y,hy⟩ := exists_evaluate_nonzero
      (fun v => (caps v).network.denote) hd b.2 (split.factors_nonzero nonzero).2
    let c := (split.scale : K)*evaluate (fun v => (caps v).network.denote) b.1 y b.2
    have hc : c ≠ 0 := mul_ne_zero split.scale.ne_zero hy
    have eqn := denote H caps N split y
    refine ⟨B.output H caps N split y,?_,c,hc,eqn⟩
    rw [eqn]
    exact Holant.LocalDrafts.Hardness.FrozenFactorNormalization.prime_scaled (Units.mk0 c hc) hp

end
end Paper2.Paper1Proved.OddUnary.CapBasis

