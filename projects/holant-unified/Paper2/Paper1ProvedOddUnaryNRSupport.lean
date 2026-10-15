import Paper2.Paper1ProvedOddUnaryNRInheritance

/-! A tensor in the sheared class has exactly the independent-set support of
disjoint complete blocks, with some coordinates pinned to zero. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

def Matches {n m : ℕ} (allowed : Fin n → Prop) (label : Fin n → Fin m)
    (x : Fin n → Bool) : Prop :=
  (∀ i,x i=true → allowed i) ∧
  (∀ i j,i≠j → x i=true → x j=true → label i≠label j)

def PartitionSupport {n : ℕ} (f : Holant.Signature K n) : Prop :=
  ∃ m,∃ allowed : Fin n → Prop,∃ label : Fin n → Fin m,
    ∀ x,f x≠0 ↔ Matches allowed label x

theorem weight_le_one_iff {n : ℕ} (x : Fin n → Bool) :
    Holant.weight x≤1 ↔ ∀ i j,x i=true → x j=true → i=j := by
  classical
  have card : Holant.weight x=(Finset.univ.filter (fun i => x i=true)).card := by
    simp only [Holant.weight,Finset.sum_boole,Nat.cast_id]
  rw [card,Finset.card_le_one]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  aesop

omit [CharZero K] in
theorem pin_live_iff {n : ℕ} {c : K} (hc : c≠0) (x : Fin n → Bool) :
    pin c x≠0 ↔ ∀ i,x i=false := by
  constructor
  · intro live
    have zero : Holant.weight x=0 := by
      by_contra nz
      exact live (by simp [pin,nz])
    have same := word_eq_zero_of_weight_zero x zero
    intro i
    simp [same]
  · intro all
    have same : x=fun _ => false := funext all
    simpa [pin,same,Holant.weight] using hc

theorem row_live_iff {n : ℕ} {c : K} (hc : c≠0) (x : Fin n → Bool) :
    row c x≠0 ↔ ∀ i j,x i=true → x j=true → i=j := by
  rw [←weight_le_one_iff]
  by_cases zero : Holant.weight x=0
  · simp [row,zero,hc]
  · by_cases one : Holant.weight x=1
    · simp [row,one,hc]
    · have high : ¬ Holant.weight x≤1 := by omega
      simp [row,zero,one,high]

omit [CharZero K] in
theorem decomposition_live_iff {n : ℕ} (D : TensorDecomposition K n)
    (x : Fin n → Bool) : D.value x≠0 ↔
    ∀ k,D.factor k (fun j => x (D.ports ⟨k,j⟩))≠0 := by
  classical
  simp [TensorDecomposition.value,Units.ne_zero D.scale,Finset.prod_ne_zero_iff]

theorem closed_partition_support {n : ℕ} {f : Holant.Signature K n}
    (hf : Closed f) (nonzero : f≠0) : PartitionSupport f := by
  classical
  rcases hf with zero|⟨D,hD,rfl⟩
  · exact False.elim (nonzero zero)
  have origin := closed_origin_live (Or.inr ⟨D,hD,rfl⟩) nonzero
  have originfactors := (decomposition_live_iff D (fun _ => false)).mp origin
  have choices : ∀ k,∃ mode : Bool,∃ c : K,
      D.factor k=(if mode then row c else pin c) := by
    intro k
    rcases hD k with ⟨_,c,eq⟩|⟨_,c,eq⟩
    · exact ⟨false,c,eq⟩
    · exact ⟨true,c,eq⟩
  choose mode c form using choices
  have cnz : ∀ k,c k≠0 := by
    intro k zero
    apply originfactors k
    rw [form k]
    cases mode k <;> simp [pin,row,zero,Holant.weight]
  let label : Fin n → Fin D.count := fun i => (D.ports.symm i).1
  let allowed : Fin n → Prop := fun i => mode (label i)=true
  have label_port (k : Fin D.count) (j : Fin (D.arity k)) :
      label (D.ports ⟨k,j⟩)=k := by simp [label]
  refine ⟨D.count,allowed,label,?_⟩
  intro x
  rw [decomposition_live_iff]
  constructor
  · intro live
    constructor
    · intro i xi
      rcases hs : D.ports.symm i with ⟨k,j⟩
      have port : D.ports ⟨k,j⟩=i := by
        simpa only [hs] using D.ports.apply_symm_apply i
      have localLive := live k
      rw [form k] at localLive
      cases hm : mode k
      · have all := (pin_live_iff (cnz k) _).mp (by simpa [hm] using localLive)
        have impossible := all j
        simp [port,xi] at impossible
      · simp [allowed,label,hs,hm]
    · intro i j ne xi xj equal
      rcases hi : D.ports.symm i with ⟨k,a⟩
      rcases hj : D.ports.symm j with ⟨l,b⟩
      have ip : D.ports ⟨k,a⟩=i := by simpa only [hi] using D.ports.apply_symm_apply i
      have jp : D.ports ⟨l,b⟩=j := by simpa only [hj] using D.ports.apply_symm_apply j
      have kl : k=l := by simpa [label,hi,hj] using equal
      subst l
      have localLive := live k
      rw [form k] at localLive
      cases hm : mode k
      · have all := (pin_live_iff (cnz k) _).mp (by simpa [hm] using localLive)
        have impossible := all a
        simp [ip,xi] at impossible
      · have unique := (row_live_iff (cnz k) _).mp (by simpa [hm] using localLive)
        have ab := unique a b (by simpa [ip] using xi) (by simpa [jp] using xj)
        apply ne
        rw [←ip,←jp,ab]
  · rintro ⟨allow,distinct⟩ k
    rw [form k]
    cases hm : mode k
    · simp only [Bool.false_eq_true,ite_false]
      apply (pin_live_iff (cnz k) _).mpr
      intro j
      cases xj : x (D.ports ⟨k,j⟩)
      · rfl
      · have impossible := allow _ xj
        simp [allowed,label_port,hm] at impossible
    · simp only [ite_true]
      apply (row_live_iff (cnz k) _).mpr
      intro a b xa xb
      by_contra ab
      have ne : D.ports ⟨k,a⟩≠D.ports ⟨k,b⟩ := by
        intro eq
        exact ab (by simpa using D.ports.injective eq)
      have different := distinct _ _ ne xa xb
      exact different (by simp [label_port])

def word {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool := fun i => decide (i∈s)

def single {n : ℕ} (i : Fin n) : Fin n → Bool := word {i}

def double {n : ℕ} (i j : Fin n) : Fin n → Bool := word {i,j}

theorem matches_single {n m : ℕ} (allowed : Fin n → Prop) (label : Fin n → Fin m)
    (i : Fin n) : Matches allowed label (single i) ↔ allowed i := by
  classical
  constructor
  · intro h
    exact h.1 i (by simp [single,word])
  · intro hi
    constructor
    · intro j hj
      have ji : j=i := by simpa [single,word] using hj
      simpa [ji] using hi
    · intro a b ne ha hb
      have ai : a=i := by simpa [single,word] using ha
      have bi : b=i := by simpa [single,word] using hb
      exact False.elim (ne (ai.trans bi.symm))

theorem matches_double {n m : ℕ} (allowed : Fin n → Prop) (label : Fin n → Fin m)
    (i j : Fin n) : Matches allowed label (double i j) ↔
      allowed i ∧ allowed j ∧ (i=j ∨ label i≠label j) := by
  classical
  constructor
  · intro h
    refine ⟨h.1 i (by simp [double,word]),h.1 j (by simp [double,word]),?_⟩
    by_cases same : i=j
    · exact Or.inl same
    · exact Or.inr (h.2 i j same (by simp [double,word]) (by simp [double,word]))
  · rintro ⟨hi,hj,sep⟩
    constructor
    · intro k hk
      have cases : k=i ∨ k=j := by simpa [double,word] using hk
      rcases cases with rfl|rfl
      · exact hi
      · exact hj
    · intro a b ne ha hb
      have ca : a=i ∨ a=j := by simpa [double,word] using ha
      have cb : b=i ∨ b=j := by simpa [double,word] using hb
      rcases ca with rfl|rfl <;> rcases cb with rfl|rfl
      · exact False.elim (ne rfl)
      · exact sep.resolve_left ne
      · exact fun eq => (sep.resolve_left (Ne.symm ne)) eq.symm
      · exact False.elim (ne rfl)

def PairwiseSupport {n : ℕ} (f : Holant.Signature K n) : Prop :=
  ∀ x,f x≠0 ↔
    (∀ i,x i=true → f (single i)≠0) ∧
    (∀ i j,i≠j → x i=true → x j=true → f (double i j)≠0)

omit [CharZero K] in
theorem partition_pairwise_support {n : ℕ} {f : Holant.Signature K n}
    (hf : PartitionSupport f) : PairwiseSupport f := by
  obtain ⟨m,allowed,label,model⟩ := hf
  intro x
  rw [model]
  constructor
  · rintro ⟨allow,distinct⟩
    constructor
    · intro i hi
      rw [model,matches_single]
      exact allow i hi
    · intro i j ne hi hj
      rw [model,matches_double]
      exact ⟨allow i hi,allow j hj,Or.inr (distinct i j ne hi hj)⟩
  · rintro ⟨singles,pairs⟩
    constructor
    · intro i hi
      exact (matches_single allowed label i).mp ((model _).mp (singles i hi))
    · intro i j ne hi hj
      have h := pairs i j ne hi hj
      rw [model,matches_double] at h
      exact h.2.2.resolve_left ne

omit [CharZero K] in
/-- Forbidden pairs on the live singleton coordinates form complete blocks:
their reflexive closure is transitive. This is the ternary obstruction used
in the sheared slice argument. -/
theorem partition_conflict_transitive {n : ℕ} {f : Holant.Signature K n}
    (hf : PartitionSupport f) (i j k : Fin n)
    (livei : f (single i)≠0) (livej : f (single j)≠0) (livek : f (single k)≠0)
    (ij : i=j ∨ f (double i j)=0) (jk : j=k ∨ f (double j k)=0) :
    i=k ∨ f (double i k)=0 := by
  obtain ⟨m,allowed,label,model⟩ := hf
  have ai : allowed i := (matches_single allowed label i).mp ((model _).mp livei)
  have aj : allowed j := (matches_single allowed label j).mp ((model _).mp livej)
  have ak : allowed k := (matches_single allowed label k).mp ((model _).mp livek)
  have equal_of_conflict (a b : Fin n) (aa : allowed a) (ab : allowed b)
      (conf : a=b ∨ f (double a b)=0) : label a=label b := by
    rcases conf with rfl|zero
    · rfl
    · by_contra ne
      have live := (model _).mpr ((matches_double allowed label a b).mpr
        ⟨aa,ab,Or.inr ne⟩)
      exact live zero
  have lij := equal_of_conflict i j ai aj ij
  have ljk := equal_of_conflict j k aj ak jk
  by_cases same : i=k
  · exact Or.inl same
  · right
    by_contra live
    have matchResult :=  (matches_double allowed label i k).mp ((model _).mp live)
    exact (matchResult.2.2.resolve_left same) (lij.trans ljk)

theorem closed_pairwise_support {n : ℕ} {f : Holant.Signature K n}
    (hf : Closed f) (nonzero : f≠0) : PairwiseSupport f :=
  partition_pairwise_support (closed_partition_support hf nonzero)

end
end Paper2.Paper1Proved.OddUnary.NR

