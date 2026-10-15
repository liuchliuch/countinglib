import Paper2.Paper1ProvedOddUnaryNRSupport
import Paper2.Paper1ProvedOddUnaryNRSlices

/-! The support reconstruction in Lemma 59: all single-coordinate slices
give a pairwise support test, and their three-coordinate tests rule out an
induced path among forbidden pairs. The resulting conflict classes are the
actual blocks of a finite partition. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [CharZero K]

theorem insert_false_single {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    i.insertNth false (single j)=single (i.succAbove j) := by
  classical
  funext q
  by_cases same : q=i
  · subst q
    simp [single,word]
  · obtain ⟨a,rfl⟩ := Fin.exists_succAbove_eq same
    simp [single,word]

theorem insert_false_double {n : ℕ} (i : Fin (n+1)) (j k : Fin n) :
    i.insertNth false (double j k)=double (i.succAbove j) (i.succAbove k) := by
  classical
  funext q
  by_cases same : q=i
  · subst q
    simp [double,word]
  · obtain ⟨a,rfl⟩ := Fin.exists_succAbove_eq same
    simp [double,word]

theorem insert_false_origin {n : ℕ} (i : Fin (n+1)) :
    i.insertNth false (fun _ => false)=(fun _ => false) := by
  funext q
  by_cases same : q=i
  · subst q;simp
  · obtain ⟨a,rfl⟩ := Fin.exists_succAbove_eq same
    simp

private theorem outside_three {n : ℕ} (i j k : Fin (n+4)) :
    ∃ q : Fin (n+4),q≠i ∧ q≠j ∧ q≠k := by
  classical
  have small : ({i,j,k} : Finset (Fin (n+4))).card ≤ 3 := by
    calc
      _ ≤ ({j,k} : Finset (Fin (n+4))).card+1 := Finset.card_insert_le _ _
      _ ≤ ({k} : Finset (Fin (n+4))).card+1+1 := Nat.add_le_add_right (Finset.card_insert_le _ _) _
      _ = 3 := by simp
  have bound : ({i,j,k} : Finset (Fin (n+4))).card < (Finset.univ : Finset (Fin (n+4))).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  obtain ⟨q,-,hq⟩ := Finset.exists_mem_notMem_of_card_lt_card bound
  exact ⟨q,by simpa using hq⟩

theorem live_of_pairs_at_zero {n : ℕ} (f : Holant.Signature K (n+1))
    (hs : ∀ i v,Closed (slice f i v)) (origin : f (fun _ => false)≠0)
    (x : Fin (n+1) → Bool) (i : Fin (n+1)) (xi : x i=false)
    (singles : ∀ j,x j=true → f (single j)≠0)
    (pairs : ∀ j k,j≠k → x j=true → x k=true → f (double j k)≠0) : f x≠0 := by
  have nz : slice f i false ≠ 0 := by
    intro zero
    apply origin
    have h := congrFun zero (fun _ => false)
    simpa only [slice,insert_false_origin,Pi.zero_apply] using h
  have localTest := closed_pairwise_support (hs i false) nz
  have result := (localTest (i.removeNth x)).mpr (by
    constructor
    · intro j hj
      rw [slice,insert_false_single]
      exact singles _ (by simpa only [Fin.removeNth_apply] using hj)
    · intro j k ne hj hk
      rw [slice,insert_false_double]
      exact pairs _ _ (fun equal => ne (Fin.succAbove_right_injective equal))
        (by simpa only [Fin.removeNth_apply] using hj) (by simpa only [Fin.removeNth_apply] using hk))
  simpa only [←xi,slice_remove] using result

theorem pairwise_of_closed_slices {n : ℕ} (f : Holant.Signature K (n+4))
    (hs : ∀ i v,Closed (slice f i v)) (nonzero : f≠0) : PairwiseSupport f := by
  classical
  have inheritance : Inheritance f := closed_slices_inheritance (n:=n+2) f hs
  obtain ⟨z,hz⟩ : ∃ z,f z≠0 := by
    by_contra none
    apply nonzero
    funext z
    by_contra live
    exact none ⟨z,live⟩
  have origin := inheritance_origin_live inheritance z hz
  intro x
  constructor
  · intro live
    constructor
    · intro i hi
      exact inheritance_support_downward inheritance x (single i) live (by
        intro j hj
        have ji : j=i := by simpa [single,word] using hj
        simpa [ji] using hi)
    · intro i j _ hi hj
      exact inheritance_support_downward inheritance x (double i j) live (by
        intro k hk
        have member : k=i ∨ k=j := by simpa [double,word] using hk
        rcases member with rfl|rfl
        · exact hi
        · exact hj)
  · rintro ⟨singles,pairs⟩
    by_cases proper : ∃ i,x i=false
    · obtain ⟨i,hi⟩ := proper
      exact live_of_pairs_at_zero f hs origin x i hi singles pairs
    · have full : ∀ i,x i=true := by
        intro i
        cases xi : x i
        · exact False.elim (proper ⟨i,xi⟩)
        · rfl
      have anyProper (y : Fin (n+4) → Bool) (zero : ∃ i,y i=false) : f y≠0 := by
        obtain ⟨i,hi⟩ := zero
        exact live_of_pairs_at_zero f hs origin y i hi
          (fun j _ => singles j (full j)) (fun j k ne _ _ => pairs j k ne (full j) (full k))
      let i : Fin (n+4) := ⟨0,by omega⟩
      have localnz : slice f i true≠0 := by
        intro zero
        have live : f (i.insertNth true (fun _ => false))≠0 := by
          obtain ⟨q,qi,-,-⟩ := outside_three i i i
          obtain ⟨a,rfl⟩ := Fin.exists_succAbove_eq qi
          exact anyProper _ ⟨i.succAbove a,by simp⟩
        apply live
        exact congrFun zero (fun _ => false)
      have localTest := closed_pairwise_support (hs i true) localnz
      have result := (localTest (i.removeNth x)).mpr (by
        constructor
        · intro j _
          change f (i.insertNth true (single j))≠0
          obtain ⟨q,qi,qj,-⟩ := outside_three i (i.succAbove j) (i.succAbove j)
          obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq qi
          apply anyProper
          refine ⟨q,?_⟩
          rw [←ha,Fin.insertNth_apply_succAbove]
          have aj : a≠j := fun eq => qj (by simpa only [eq] using ha.symm)
          simp [single,word,aj]
        · intro j k _ _ _
          change f (i.insertNth true (double j k))≠0
          obtain ⟨q,qi,qj,qk⟩ := outside_three i (i.succAbove j) (i.succAbove k)
          obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq qi
          apply anyProper
          refine ⟨q,?_⟩
          rw [←ha,Fin.insertNth_apply_succAbove]
          have aj : a≠j := fun eq => qj (by simpa [eq] using ha.symm)
          have ak : a≠k := fun eq => qk (by simpa [eq] using ha.symm)
          simp [double,word,aj,ak])
      have result' : slice f i (x i) (i.removeNth x)≠0 := by rw [full];exact result
      change f (i.insertNth (x i) (i.removeNth x))≠0 at result'
      rw [Fin.insertNth_removeNth] at result'
      simpa using result'

theorem conflict_transitive_of_closed_slices {n : ℕ} (f : Holant.Signature K (n+4))
    (hs : ∀ i v,Closed (slice f i v))
    (i j k : Fin (n+4))
    (li : f (single i)≠0) (lj : f (single j)≠0) (lk : f (single k)≠0)
    (ij : i=j ∨ f (double i j)=0) (jk : j=k ∨ f (double j k)=0) :
    i=k ∨ f (double i k)=0 := by
  obtain ⟨q,qi,qj,qk⟩ := outside_three i j k
  obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq (Ne.symm qi)
  obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq (Ne.symm qj)
  obtain ⟨c,hc⟩ := Fin.exists_succAbove_eq (Ne.symm qk)
  have qnz : slice f q false≠0 := by
    intro zero
    apply li
    simpa only [slice,insert_false_single,ha,Pi.zero_apply] using congrFun zero (single a)
  have model := closed_partition_support (hs q false) qnz
  have la : slice f q false (single a)≠0 := by simpa only [slice,insert_false_single,ha] using li
  have lb : slice f q false (single b)≠0 := by simpa only [slice,insert_false_single,hb] using lj
  have lc : slice f q false (single c)≠0 := by simpa only [slice,insert_false_single,hc] using lk
  have ab : a=b ∨ slice f q false (double a b)=0 := by
    rcases ij with equal|zero
    · exact Or.inl (Fin.succAbove_right_injective (ha.trans (equal.trans hb.symm)))
    · exact Or.inr (by simpa only [slice,insert_false_double,ha,hb] using zero)
  have bc : b=c ∨ slice f q false (double b c)=0 := by
    rcases jk with equal|zero
    · exact Or.inl (Fin.succAbove_right_injective (hb.trans (equal.trans hc.symm)))
    · exact Or.inr (by simpa only [slice,insert_false_double,hb,hc] using zero)
  rcases partition_conflict_transitive model a b c la lb lc ab bc with equal|zero
  · exact Or.inl (ha.symm.trans ((congrArg q.succAbove equal).trans hc))
  · exact Or.inr (by simpa only [slice,insert_false_double,ha,hc] using zero)

omit [CharZero K] in
theorem double_comm {n : ℕ} (i j : Fin n) : double i j=double j i := by
  simp only [double,Finset.pair_comm]

def Conflict {n : ℕ} (f : Holant.Signature K n) (i j : Fin n) : Prop :=
  i=j ∨ (f (single i)≠0 ∧ f (single j)≠0 ∧ f (double i j)=0)

omit [CharZero K] in
theorem partition_of_pairwise_conflict {n : ℕ} (f : Holant.Signature K n)
    (pairwise : PairwiseSupport f)
    (transitive : ∀ i j k,f (single i)≠0 → f (single j)≠0 → f (single k)≠0 →
      (i=j ∨ f (double i j)=0) → (j=k ∨ f (double j k)=0) → i=k ∨ f (double i k)=0) :
    PartitionSupport f := by
  classical
  let S : Setoid (Fin n) := {
    r := Conflict f
    iseqv := {
      refl := fun i => Or.inl rfl
      symm := by
        intro i j h
        rcases h with equal|⟨li,lj,zero⟩
        · exact Or.inl equal.symm
        · exact Or.inr ⟨lj,li,by simpa only [double_comm] using zero⟩
      trans := by
        intro i j k h1 h2
        rcases h1 with rfl|⟨li,lj,ij⟩
        · exact h2
        rcases h2 with rfl|⟨-,lk,jk⟩
        · exact Or.inr ⟨li,lj,ij⟩
        rcases transitive i j k li lj lk (Or.inr ij) (Or.inr jk) with equal|zero
        · exact Or.inl equal
        · exact Or.inr ⟨li,lk,zero⟩ } }
  let : Fintype (Quotient S) := Fintype.ofFinite (Quotient S)
  let label : Fin n → Fin (Fintype.card (Quotient S)) :=
    fun i => (Fintype.equivFin (Quotient S)) (Quotient.mk S i)
  have labels (i j : Fin n) : label i=label j ↔ Conflict f i j := by
    change (Fintype.equivFin (Quotient S)) (Quotient.mk S i)=
      (Fintype.equivFin (Quotient S)) (Quotient.mk S j) ↔ _
    rw [Equiv.apply_eq_iff_eq]
    exact ⟨Quotient.exact,fun h => @Quotient.sound _ S i j h⟩
  refine ⟨Fintype.card (Quotient S),(fun i => f (single i)≠0),label,?_⟩
  intro x
  rw [pairwise x]
  constructor
  · rintro ⟨singles,pairs⟩
    refine ⟨singles,?_⟩
    intro i j ne hi hj equal
    rcases (labels i j).mp equal with same|⟨-,-,zero⟩
    · exact ne same
    · exact pairs i j ne hi hj zero
  · rintro ⟨singles,distinct⟩
    refine ⟨singles,?_⟩
    intro i j ne hi hj zero
    exact distinct i j ne hi hj ((labels i j).mpr (Or.inr ⟨singles i hi,singles j hj,zero⟩))

theorem partition_support_of_closed_slices {n : ℕ} (f : Holant.Signature K (n+4))
    (hs : ∀ i v,Closed (slice f i v)) (nonzero : f≠0) : PartitionSupport f :=
  partition_of_pairwise_conflict f (pairwise_of_closed_slices f hs nonzero)
    (conflict_transitive_of_closed_slices f hs)

end
end Paper2.Paper1Proved.OddUnary.NR

