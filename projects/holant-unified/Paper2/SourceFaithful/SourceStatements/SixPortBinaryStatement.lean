import Paper2.HeightOne.Dihedral.SixPortAllCards
import Holant.Proofs.FiniteGroups.Stabilization.BinaryPrimes
import Paper2.Tractable.Anchor.MatrixActions
import Paper2.HeightOne.Dihedral.SixPortActual
import Paper2.HeightOne.PhaseCards.ProductPresentation

/-! Source Theorem 5.14 with the retained number and nonzero determinants
of all binary factors. The theorem is purely about the original tensor:
no finite language, preprocessing, minimum-prime or realization premise
is supplied. Nonzero logical ratios are retained through analytic xor
shifts and the invertible Walsh action on every original factor. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.SourceStatements.SixPortBinary
noncomputable section
open Paper2.HeightOne Paper2.HeightOne.Dihedral Paper2.HeightOne.Cyclic
open Paper2.Tractable Paper2.ExactInput Paper2.EndpointSelfLoop
open Paper2.HeightOne.PhaseCards Paper2.HeightOne.Dihedral.SixPortSupport
open Paper2.HeightOne.Dihedral.SixPortPencils
open Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
local instance {ι : Type} : DecidableEq ι := Classical.decEq ι

/-- The factor really has arity two, and its actual ordered matrix has
nonzero determinant. The cast retains its two original ordered ports. -/
def BinaryNonsingular {m : ℕ} (g : Signature AlgebraicComplex m) : Prop :=
  ∃ h : m=2, Matrix.det (fun p q : Bool =>
    g (fun j => ![p,q] (Fin.cast h j))) ≠ 0

/-- Three nonsingular factors with an actual disjoint ordered port map and
nonzero global normalization. The normalization may be absorbed into a
binary factor without changing nonsingularity. -/
def ThreeNonsingularBinaryProduct (f : Signature AlgebraicComplex 6) : Prop :=
  ∃ D : TensorDecomposition AlgebraicComplex 6,
    D.count=3 ∧ D.value=f ∧ ∀ i, BinaryNonsingular (D.factor i)

lemma source5_14_xor_eval (a : Fin 2 → Bool) (g : Signature AlgebraicComplex 2)
    (p q : Bool) : xorShift a g ![p,q] = g ![a 0 ^^ p,a 1 ^^ q] := by
  apply congrArg g
  funext j
  fin_cases j <;> rfl

lemma source5_14_xor_det (a : Fin 2 → Bool) (g : Signature AlgebraicComplex 2) :
    Matrix.det (binaryMatrix (xorShift a g)) =
      if a 0=a 1 then Matrix.det (binaryMatrix g) else -Matrix.det (binaryMatrix g) := by
  simp only [binary_det_formula,binaryMatrix,source5_14_xor_eval]
  cases a 0 <;> cases a 1 <;> simp <;> ring

lemma source5_14_xor_nonsingular {m : ℕ} (a : Fin m → Bool)
    (g : Signature AlgebraicComplex m) (hg : BinaryNonsingular g) :
    BinaryNonsingular (xorShift a g) := by
  obtain ⟨h,hg⟩ := hg
  subst m
  refine ⟨rfl,?_⟩
  change Matrix.det (binaryMatrix (xorShift a g)) ≠ 0
  change Matrix.det (binaryMatrix g) ≠ 0 at hg
  rw [source5_14_xor_det]
  split_ifs <;> simpa using hg

lemma source5_14_walsh_det (g : Signature AlgebraicComplex 2) :
    Matrix.det (binaryMatrix (Signature.coordinateAction (fun _ => walsh) g)) =
      4 * Matrix.det (binaryMatrix g) := by
  have hrep : g=kernelSignature (binaryMatrix g) :=
    (binarySignature_binaryMatrix g).symm
  have hact : Signature.coordinateAction (fun _ => walsh) g =
      kernelSignature (Kernel.mul (Kernel.mul walsh (binaryMatrix g))
        (Kernel.transpose walsh)) := by
    conv_lhs => rw [hrep,Paper2.Tractable.coordinateAction_kernelSignature]
  have hm : binaryMatrix (Signature.coordinateAction (fun _ => walsh) g) =
      walsh * binaryMatrix g * walsh.transpose := by
    rw [hact]
    ext p q
    rfl
  have hw : Matrix.det walsh=(-2 : AlgebraicComplex) := by
    rw [binary_det_formula]
    norm_num [walsh]
  rw [hm,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hw]
  ring

lemma source5_14_walsh_nonsingular {m : ℕ} (g : Signature AlgebraicComplex m)
    (hg : BinaryNonsingular g) :
    BinaryNonsingular (Signature.coordinateAction (fun _ => walsh) g) := by
  obtain ⟨h,hg⟩ := hg
  subst m
  refine ⟨rfl,?_⟩
  change Matrix.det (binaryMatrix (Signature.coordinateAction (fun _ => walsh) g)) ≠ 0
  change Matrix.det (binaryMatrix g) ≠ 0 at hg
  rw [source5_14_walsh_det]
  exact mul_ne_zero (by norm_num) hg

 theorem source5_14_origin (f : Signature AlgebraicComplex 6)
    (h0 : f (fun _ => false) ≠ 0) (s t u : AlgebraicComplex)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hmatching : ∀ a b (hab : a ≠ b), ∀ q, q=s ∨ q=t ∨ q=u →
      plusContraction a b hab q f ≠ 0 → EqualityMatchingSupport (plusContraction a b hab q f))
    (hproduct : ∀ a b (hab : a ≠ b), ∀ q, q=s ∨ q=t ∨ q=u →
      Product (Tensor.reindex (Fintype.equivFin (Remaining a b)) (plusContraction a b hab q f))) :
    ThreeNonsingularBinaryProduct f := by
  have hf : f≠0 := by intro h; exact h0 (congrFun h (fun _ => false))
  let S : Set AlgebraicComplex := {q | q=s ∨ q=t ∨ q=u}
  have hthree : ∃ x∈S,∃ y∈S,∃ z∈S,x≠y ∧ x≠z ∧ y≠z :=
    ⟨s,Or.inl rfl,t,Or.inr (Or.inl rfl),u,Or.inr (Or.inr rfl),hst,hsu,htu⟩
  obtain ⟨P,_,hP⟩ := matching_core_of_cards f hf (by decide) S hthree hmatching hproduct
  have hcount : P.count=3 := by have h:=Matching.pair_count P; omega
  obtain ⟨ρ,hρne,hρ⟩ := logical_three_factorization f P hcount hP h0 s t u hst hsu htu
    hmatching hproduct
  refine ⟨equalityDecomposition P (f (fun _ => false)) h0 ρ,hcount,
    decomposition_of_logical_product f P hP h0 ρ hρ,?_⟩
  intro i
  refine ⟨rfl,?_⟩
  change Matrix.det (binaryMatrix (equalityBinary (ρ i))) ≠ 0
  rw [binary_det_formula]
  simpa [binaryMatrix,equalityBinary] using hρne i

 theorem source5_14_shifted (f : Signature AlgebraicComplex 6)
    (a : Fin 6 → Bool) (ha : f a ≠ 0) (s t u : AlgebraicComplex)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hmatching : ∀ i j (hij : i ≠ j),∀ q,q=s ∨ q=t ∨ q=u →
      plusContraction i j hij q (xorShift a f) ≠ 0 →
        EqualityMatchingSupport (plusContraction i j hij q (xorShift a f)))
    (hproduct : ∀ i j (hij : i ≠ j),∀ q,q=s ∨ q=t ∨ q=u →
      Product (Tensor.reindex (Fintype.equivFin (Remaining i j))
        (plusContraction i j hij q (xorShift a f)))) :
    ThreeNonsingularBinaryProduct f := by
  obtain ⟨D,hcount,hD,hn⟩ := source5_14_origin (xorShift a f)
    (by rwa [xorShift_origin]) s t u hst hsu htu hmatching hproduct
  refine ⟨shiftedDecomposition D a,hcount,?_,?_⟩
  · rw [shiftedDecomposition_value,hD,xorShift_involutive]
  · intro i
    exact source5_14_xor_nonsingular _ _ (hn i)

theorem source5_14_all_xor_cards (f : Signature AlgebraicComplex 6)
    (a : Fin 6 → Bool) (ha : f a ≠ 0) (s t u : AlgebraicComplex)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0)
    (hcoset : ∀ i j (hij : i ≠ j) v w q, q = s ∨ q = t ∨ q = u →
      card (xorKernel v w q) i j hij f ≠ 0 →
        CosetMatchingSupport (card (xorKernel v w q) i j hij f))
    (hprod : ∀ i j (hij : i ≠ j) v w q, q = s ∨ q = t ∨ q = u →
      Product (Tensor.reindex (Fintype.equivFin (Remaining i j))
        (card (xorKernel v w q) i j hij f))) :
    ThreeNonsingularBinaryProduct f := by
  classical
  let g := xorShift a f
  let S : Finset AlgebraicComplex := {s,t,u}
  have hS : S.card = 3 := by simp [S,hst,hsu,htu]
  have hSmem (q : AlgebraicComplex) : q ∈ S ↔ q = s ∨ q = t ∨ q = u := by simp [S]
  have hsne : ∀ q ∈ S,q ≠ 0 := by
    intro q hq
    rcases (hSmem q).mp hq with rfl | rfl | rfl <;> assumption
  have hc : ∀ i j (hij : i ≠ j) v w q, q ∈ S →
      card (xorKernel v w q) i j hij g ≠ 0 →
        CosetMatchingSupport (card (xorKernel v w q) i j hij g) := by
    intro i j hij v w q hq hn
    change card (xorKernel v w q) i j hij (xorShift a f) ≠ 0 at hn
    rw [card_xorShift] at hn
    have ho : card (xorKernel (a i ^^ v) (a j ^^ w) q) i j hij f ≠ 0 := by
      intro hz
      rw [hz] at hn
      exact hn rfl
    change CosetMatchingSupport (card (xorKernel v w q) i j hij (xorShift a f))
    rw [card_xorShift]
    exact (hcoset i j hij _ _ q ((hSmem q).mp hq) ho).xorShift _
  let phases : Fin 3 → AlgebraicComplex := ![s,t,u]
  have hphases : Function.Injective phases := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [phases]
  have hp : HasParity g := by
    apply hasParity_of_nonzero_three_phase_contractions (by simp) phases hphases g
    intro i j hij k hn
    have hq : phases k ∈ S := by fin_cases k <;> simp [phases,S]
    rw [← card_plus (phases k) i j hij g] at hn ⊢
    rw [← xorKernel_false_false] at hn ⊢
    exact (hc i j hij false false (phases k) hq hn).hasParity
  have hcards : ∀ p ξ q, q ∈ S →
      (pencilSupport (first g p ξ) (second g p ξ) q).card ≤ 4 := by
    intro p ξ q hq
    let H := card (xorKernel false ξ q) (p 0) (p 1) (pair_ports_ne p) g
    have he := ordered_pencil_card g p ξ q
    by_cases hn : H = 0
    · have hz : (fun r => first g p ξ r - q * second g p ξ r) = 0 := by
        rw [he]
        change Tensor.reindex (tailEquiv p).symm H = 0
        rw [hn]
        rfl
      have hz' : pencilSupport (first g p ξ) (second g p ξ) q = ∅ := by
        ext r
        have hh : first g p ξ r - q * second g p ξ r = 0 := congrFun hz r
        simp [hh]
      rw [hz']
      simp
    · have hh := (hc (p 0) (p 1) (pair_ports_ne p) false ξ q hq hn).card
      have hrem : Fintype.card (Remaining (p 0) (p 1)) = 4 := by
        have hh := remaining_card (p 0) (p 1) (pair_ports_ne p)
        simp only [Fintype.card_fin] at hh
        omega
      have hh' : (Cyclic.support H).card = 4 := by simpa [hrem,H] using hh
      have hsupport : pencilSupport (first g p ξ) (second g p ξ) q =
          Cyclic.support (fun r => first g p ξ r - q * second g p ξ r) := by
        ext r
        simp [pencilSupport,Cyclic.support]
      rw [hsupport]
      rw [he,support_reindex_card]
      exact hh'.le
  have hcomp : ∀ p ξ q, q ∈ S → ∀ r ∈ pencilSupport (first g p ξ) (second g p ξ) q,
      complement r ∈ pencilSupport (first g p ξ) (second g p ξ) q := by
    intro p ξ q hq r hr
    let H := card (xorKernel false ξ q) (p 0) (p 1) (pair_ports_ne p) g
    have he := ordered_pencil_card g p ξ q
    have hr' : H (fun k => r ((tailEquiv p).symm k)) ≠ 0 := by
      rw [mem_pencilSupport] at hr
      have hrr := congrFun he r
      change first g p ξ r - q * second g p ξ r = H (fun k => r ((tailEquiv p).symm k)) at hrr
      rwa [hrr] at hr
    have hn : H ≠ 0 := by intro hz; exact hr' (congrFun hz _)
    have hh := (hc (p 0) (p 1) (pair_ports_ne p) false ξ q hq hn).complement _ hr'
    rw [mem_pencilSupport]
    change (fun x => first g p ξ x - q * second g p ξ x) (complement r) ≠ 0
    rw [he]
    exact hh
  have hbound : ∀ p ξ, (jointSupport (first g p ξ) (second g p ξ)).card ≤ 4 :=
    ordered_three_phase_union g hp S hS hsne hcards hcomp
  have hmatch : ∀ i j (hij : i ≠ j), ∀ q, q = s ∨ q = t ∨ q = u →
      plusContraction i j hij q g ≠ 0 → EqualityMatchingSupport (plusContraction i j hij q g) := by
    intro i j hij q hq hn
    let p := pairPerm i j
    have hU : (jointSupport
        (fun x => g (extendBits i j hij x false false))
        (fun x => g (extendBits i j hij x true true))).card ≤ 4 := by
      have hh := hbound p false
      have hp0 : p 0 = i := pairPerm_zero i j hij
      have hp1 : p 1 = j := pairPerm_one i j
      rwa [equal_joint_card_as g p i j hij hp0 hp1] at hh
    have hrem : Fintype.card (Remaining i j) = 4 := by
      have hh := remaining_card i j hij
      simp only [Fintype.card_fin] at hh
      omega
    have hco : CosetMatchingSupport (plusContraction i j hij q g) := by
      rw [← card_plus q i j hij g,← xorKernel_false_false] at hn ⊢
      exact hc i j hij false false q ((hSmem q).mpr hq) hn
    have h0 : g (extendBits i j hij (fun _ => false) false false) ≠ 0 := by
      rw [extendBits_origin_false]
      change xorShift a f (fun _ => false) ≠ 0
      rwa [xorShift_origin]
    have hplus : plusContraction i j hij q g =
        (fun x => g (extendBits i j hij x false false) - q * g (extendBits i j hij x true true)) := by
      funext x
      exact plusContraction_apply i j hij q g x
    have hh := matching_pencil_of_union_bound
      (fun x => g (extendBits i j hij x false false))
      (fun x => g (extendBits i j hij x true true)) q (Or.inl h0)
      (by simpa [hrem] using hU) (by rwa [← hplus])
    rwa [← hplus] at hh
  apply source5_14_shifted f a ha s t u hst hsu htu hmatch
  intro i j hij q hq
  rw [plusContraction_xorShift,reindex_xorShift]
  exact product_xorShift (hprod i j hij (a i) (a j) q hq) _


/-- The literal source B_N class: zero, or a partition entirely into
pairs, each pair an offset two-point phase block. D.ports retains the
original port order and D.scale retains the arbitrary nonzero scalar. -/
def BinaryPhaseProduct (N : ℕ) {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  f = 0 ∨ ∃ D : TensorDecomposition AlgebraicComplex n,
    (∀ i, D.arity i = 2 ∧ EvenPhaseBlock N (D.factor i)) ∧ D.value = f

lemma source5_14_binaryPhase_scale {N n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : BinaryPhaseProduct N f) (c : AlgebraicComplex) : BinaryPhaseProduct N (c • f) := by
  by_cases hc : c = 0
  · subst c
    exact Or.inl (by simp)
  rcases hf with rfl | ⟨D,hD,rfl⟩
  · exact Or.inl (by simp)
  let Q : TensorDecomposition AlgebraicComplex n := {D with scale := Units.mk0 c hc * D.scale}
  refine Or.inr ⟨Q,hD,?_⟩
  funext x
  simp [Q,TensorDecomposition.value,mul_assoc]

lemma source5_14_twoPoint_support (a x : Fin 2 → Bool) (r : AlgebraicComplex)
    (hr : r ≠ 0) : twoPoint a r x ≠ 0 ↔ Bool.xor (x 0) (x 1) = Bool.xor (a 0) (a 1) := by
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases ha0 : a 0 <;> cases ha1 : a 1 <;>
    simp [twoPoint,point,funext_iff,Fin.forall_fin_two,hx0,hx1,ha0,ha1,hr]

lemma source5_14_block_support {N m : ℕ} (g : Signature AlgebraicComplex m)
    (h2 : m = 2) (hg : EvenPhaseBlock N g) :
    ∃ d : Bool, ∀ x, g x ≠ 0 ↔
      Bool.xor (x (Fin.cast h2.symm 0)) (x (Fin.cast h2.symm 1)) = d := by
  subst m
  obtain ⟨k,a,r,_,hr,rfl⟩ := hg
  exact ⟨Bool.xor (a 0) (a 1),fun x => source5_14_twoPoint_support a x r hr.ne_zero⟩

lemma source5_14_binaryPhase_product {N n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : BinaryPhaseProduct N f) : Product f := by
  rcases hf with rfl | ⟨D,hD,rfl⟩
  · exact product_zero n
  · exact Product.decomposition D (fun i => (hD i).2.product)

lemma source5_14_binaryPhase_coset {N : ℕ} {ι : Type} [Fintype ι]
    (f : Tensor AlgebraicComplex ι)
    (hf : BinaryPhaseProduct N (Tensor.reindex (Fintype.equivFin ι) f))
    (hn : f ≠ 0) : CosetMatchingSupport f := by
  rcases hf with hz | ⟨D,hD,hvalue⟩
  · apply False.elim (hn ?_)
    funext x
    have hh := congrFun hz (fun j => x ((Fintype.equivFin ι).symm j))
    simpa only [Tensor.reindex_apply,Equiv.symm_apply_apply,Pi.zero_apply] using hh
  · have hd : ∀ i, ∃ d : Bool, ∀ x, D.factor i x ≠ 0 ↔
        Bool.xor (x (Fin.cast (hD i).1.symm 0)) (x (Fin.cast (hD i).1.symm 1)) = d :=
      fun i => source5_14_block_support (D.factor i) (hD i).1 (hD i).2
    choose d hd using hd
    have hh := decomposition_matching_coset D (fun i => (hD i).1) d hd
    refine ⟨decompositionPairing D (fun i => (hD i).1),
      Matching.word (decompositionPairing D (fun i => (hD i).1)) d (fun _ => false),?_⟩
    rw [← hvalue,hh,cosetCode_matchingWords]

/-- The source's oriented phase/reflection hypothesis expressed in the exact
normalized Walsh kernels. Both original deleted-port orders are quantified;
zero cards belong to B_N. There are no language, processing, group-classification
or realization hypotheses on f. -/
def SourceContractions (N : ℕ) (f : Signature AlgebraicComplex 6) : Prop :=
  ∀ i j (hij : i ≠ j) (q : AlgebraicComplex), q ^ N = 1 →
    BinaryPhaseProduct N (Tensor.reindex (Fintype.equivFin (Remaining i j))
      (card (PhaseCards.plusKernel q) i j hij (walshCoordinates f))) ∧
    BinaryPhaseProduct N (Tensor.reindex (Fintype.equivFin (Remaining i j))
      (card (minusKernel q) i j hij (walshCoordinates f)))

lemma source5_14_oriented_xor {N : ℕ} (hN : 0 < N)
    {f : Signature AlgebraicComplex 6} (h : SourceContractions N f)
    (i j : Fin 6) (hij : i ≠ j) (v w : Bool) (q : AlgebraicComplex) (hq : q ^ N = 1) :
    BinaryPhaseProduct N (Tensor.reindex (Fintype.equivFin (Remaining i j))
      (card (xorKernel v w q) i j hij (walshCoordinates f))) := by
  have hq0 : q ≠ 0 := by intro hz; simp [hz,Nat.ne_of_gt hN] at hq
  have hf (w : Bool) (q : AlgebraicComplex) (hq : q ^ N = 1) :
      BinaryPhaseProduct N (Tensor.reindex (Fintype.equivFin (Remaining i j))
        (card (xorKernel false w q) i j hij (walshCoordinates f))) := by
    cases w
    · simpa only [xorKernel_false_false] using (h i j hij q hq).1
    · simpa only [xorKernel_false_true] using (h i j hij q hq).2
  cases v
  · exact hf w q hq
  · rw [xorKernel_reverse w q hq0]
    have hi : q⁻¹ ^ N = 1 := by rw [inv_pow,hq,inv_one]
    have hh := source5_14_binaryPhase_scale (hf (!w) q⁻¹ hi) (-q)
    convert hh using 1
    funext x
    unfold card
    rw [contractKernel_scale]
    rfl

/-- Source Theorem 5.14. The conclusion retains exactly three actual
nonsingular binary factors of the original signature. The proof is stronger
than the source with respect to N: oddness is unnecessary once the literal
B_N contraction hypothesis is supplied. -/
theorem source5_14_scaled (N : ℕ) (hN : 3 ≤ N) (f : Signature AlgebraicComplex 6)
    (hcards : SourceContractions N f) : f = 0 ∨ ThreeNonsingularBinaryProduct f := by
  classical
  by_cases hf : f = 0
  · exact Or.inl hf
  right
  let : NeZero N := ⟨by omega⟩
  have hw := walsh_nonzero f hf
  obtain ⟨a,ha⟩ : ∃ a,walshCoordinates f a ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  obtain ⟨s,hs,t,ht,u,hu,hst,hsu,htu⟩ := three_algebraic_root_phases N hN
  have H (q : AlgebraicComplex) (hq : q ^ N = 1) : q ≠ 0 := by
    intro hz
    simp [hz,NeZero.ne N] at hq
  have hqroot : ∀ q : AlgebraicComplex,q = s ∨ q = t ∨ q = u → q ^ N = 1 := by
    intro q hq
    rcases hq with rfl | rfl | rfl <;> assumption
  obtain ⟨D,hcount,hD,hn⟩ := source5_14_all_xor_cards (walshCoordinates f)
    a ha s t u hst hsu htu (H s hs) (H t ht) (H u hu)
    (fun i j hij v w q hq hz => source5_14_binaryPhase_coset _
      (source5_14_oriented_xor (by omega) hcards i j hij v w q (hqroot q hq)) hz)
    (fun i j hij v w q hq => source5_14_binaryPhase_product
      (source5_14_oriented_xor (by omega) hcards i j hij v w q (hqroot q hq)))
  refine ⟨D.mapAction walsh,hcount,?_,?_⟩
  · rw [TensorDecomposition.value_mapAction,hD]
    change walshBasis.action (walshCoordinates f) = f
    rw [← walshBasis_inverse_action,InvertibleKernel.action_symm_action]
  · intro i
    exact source5_14_walsh_nonsingular (D.factor i) (hn i)


lemma source5_14_scale_nonsingular {m : ℕ} (c : AlgebraicComplex) (hc : c ≠ 0)
    (g : Signature AlgebraicComplex m) (hg : BinaryNonsingular g) :
    BinaryNonsingular (c • g) := by
  obtain ⟨h,hg⟩ := hg
  subst m
  refine ⟨rfl,?_⟩
  change Matrix.det (binaryMatrix (c • g)) ≠ 0
  change Matrix.det (binaryMatrix g) ≠ 0 at hg
  have he : Matrix.det (binaryMatrix (c • g)) = c ^ 2 * Matrix.det (binaryMatrix g) := by
    rw [binary_det_formula,binary_det_formula]
    simp only [binaryMatrix,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ hc) hg

/-- The literal normalized tensor product has no external scalar: all
normalization is absorbed into one of the three nonsingular binary factors. -/
def LiteralThreeNonsingularBinaryProduct (f : Signature AlgebraicComplex 6) : Prop :=
  ∃ D : TensorDecomposition AlgebraicComplex 6,
    D.count = 3 ∧ D.scale = 1 ∧ D.value = f ∧ ∀ i, BinaryNonsingular (D.factor i)

lemma source5_14_absorb_scalar {f : Signature AlgebraicComplex 6}
    (hf : ThreeNonsingularBinaryProduct f) : LiteralThreeNonsingularBinaryProduct f := by
  classical
  obtain ⟨D,hcount,hvalue,hn⟩ := hf
  let i₀ : Fin D.count := ⟨0,by omega⟩
  let Q : TensorDecomposition AlgebraicComplex 6 :=
    {D with
      scale := 1
      factor := fun i => (if i = i₀ then (D.scale : AlgebraicComplex) else 1) • D.factor i}
  refine ⟨Q,hcount,rfl,?_,?_⟩
  · rw [← hvalue]
    funext x
    simp only [Q,TensorDecomposition.value,Units.val_one,one_mul,
      Pi.smul_apply,smul_eq_mul]
    rw [Finset.prod_mul_distrib]
    simp
  · intro i
    apply source5_14_scale_nonsingular _ _ _ (hn i)
    split_ifs
    · exact Units.ne_zero D.scale
    · exact one_ne_zero

/-- Source Theorem 5.14 with an exact product of three nonsingular binaries
of the original six-port signature. Oddness is not needed once the source's
literal pair-partition contraction hypothesis is present. -/
theorem source_5_14 (N : ℕ) (hN : 3 ≤ N) (f : Signature AlgebraicComplex 6)
    (hcards : SourceContractions N f) : f = 0 ∨ LiteralThreeNonsingularBinaryProduct f := by
  rcases source5_14_scaled N hN f hcards with h | h
  · exact Or.inl h
  · exact Or.inr (source5_14_absorb_scalar h)


end
end Paper2.SourceFaithful.SourceStatements.SixPortBinary


