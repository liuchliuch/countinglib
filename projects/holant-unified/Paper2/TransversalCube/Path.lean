import Paper2.GadgetTrace
import Paper2.WeightedMatching

namespace Paper2.TransversalCube
open scoped BigOperators

abbrev Ports (m : ℕ) := Fin (m + 1) × Bool
abbrev Edges (m : ℕ) := Fin m × Bool

def leftWord {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool) : Ports m → Bool :=
  fun i => Fin.cases (if i.2 then x 1 else x 0) (fun j => z (j, i.2)) i.1

def rightWord {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool) : Ports m → Bool :=
  fun i => if i.2 then Fin.lastCases (x 3) (fun j => !(z (j, false))) i.1
    else Fin.cases (x 2) (fun j => !(z (j, true))) i.1

def Opposite {m : ℕ} (w : Ports m → Bool) : Prop :=
  ∀ j, w (j, true) = !(w (j, false))

def centerWord {m : ℕ} (t : Bool) : Edges m → Bool :=
  fun i => if i.2 then !t else t

@[simp] lemma leftWord_zero {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool) (b : Bool) :
    leftWord x z (0, b) = if b then x 1 else x 0 := rfl
@[simp] lemma leftWord_succ {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool)
    (i : Fin m) (b : Bool) : leftWord x z (i.succ, b) = z (i,b) := rfl
@[simp] lemma rightWord_zero_false {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool) :
    rightWord x z (0, false) = x 2 := rfl
@[simp] lemma rightWord_succ_false {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool)
    (i : Fin m) : rightWord x z (i.succ, false) = !(z (i,true)) := rfl
@[simp] lemma rightWord_last_true {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool) :
    rightWord x z (Fin.last m, true) = x 3 := by simp [rightWord]
@[simp] lemma rightWord_castSucc_true {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool)
    (i : Fin m) : rightWord x z (i.castSucc, true) = !(z (i,false)) := by simp [rightWord]

lemma left_opposite {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool) :
    Opposite (leftWord x z) ↔ x 1 = !(x 0) ∧ ∀ i, z (i,true) = !(z (i,false)) := by
  simp [Opposite, Fin.forall_fin_succ]

lemma center_unique {m : ℕ} (hm : 0 < m) (x : Fin 4 → Bool) (z : Edges m → Bool)
    (hl : Opposite (leftWord x z)) (hr : Opposite (rightWord x z)) :
    x 1 = !(x 0) ∧ x 3 = !(x 2) ∧ z = centerWord (x 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨hx, hz⟩ := (left_opposite x z).1 hl
  have hbase : z (0,false) = x 2 := by
    have h := hr 0
    have he : (0 : Fin (m+1)).castSucc = (0 : Fin (m+1+1)) := rfl
    rw [← he, rightWord_castSucc_true] at h
    simpa using congrArg Bool.not h
  have hconst : ∀ i : Fin (m+1), z (i,false) = x 2 := by
    intro i
    induction i using Fin.induction with
    | zero => exact hbase
    | succ i ih =>
      have h := hr i.succ.castSucc
      have he : i.succ.castSucc = i.castSucc.succ := rfl
      rw [rightWord_castSucc_true, he, rightWord_succ_false, hz] at h
      simpa using (congrArg Bool.not h).trans (by simpa using ih)
  have hz' : z = centerWord (x 2) := by
    funext i
    rcases i with ⟨i,b⟩
    cases b <;> simp [centerWord, hconst, hz]
  refine ⟨hx, ?_, hz'⟩
  have h := hr (Fin.last (m+1))
  have he : Fin.last (m+1) = (Fin.last m).succ := rfl
  rw [rightWord_last_true, he, rightWord_succ_false, hz, Bool.not_not, hconst] at h
  exact h

lemma center_exists {m : ℕ} (x : Fin 4 → Bool) (h01 : x 1 = !(x 0))
    (h23 : x 3 = !(x 2)) :
    Opposite (leftWord x (centerWord (x 2) : Edges m → Bool)) ∧
    Opposite (rightWord x (centerWord (x 2) : Edges m → Bool)) := by
  constructor
  · rw [left_opposite]
    exact ⟨h01, fun _ => rfl⟩
  · intro j
    have hfalse : rightWord x (centerWord (x 2) : Edges m → Bool) (j,false) = x 2 := by
      induction j using Fin.cases <;> simp [centerWord]
    rw [hfalse]
    induction j using Fin.lastCases <;> simp [centerWord, h23]

lemma left_constant {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool) (t : Bool) :
    leftWord x z = (fun _ => t) ↔ x 0 = t ∧ x 1 = t ∧ z = (fun _ => t) := by
  constructor
  · intro h
    refine ⟨by simpa using congrFun h (0,false), by simpa using congrFun h (0,true), ?_⟩
    funext i
    simpa using congrFun h (i.1.succ,i.2)
  · rintro ⟨h0,h1,rfl⟩
    funext i
    rcases i with ⟨j,b⟩
    induction j using Fin.cases <;> cases b <;> simp_all

lemma right_constant {m : ℕ} (x : Fin 4 → Bool) (z : Edges m → Bool) (t : Bool) :
    rightWord x z = (fun _ => t) ↔ x 2 = t ∧ x 3 = t ∧ z = (fun _ => !t) := by
  constructor
  · intro h
    refine ⟨by simpa using congrFun h (0,false), by simpa using congrFun h (Fin.last m,true), ?_⟩
    funext i
    rcases i with ⟨i,b⟩
    cases b
    · have h' := congrFun h (i.castSucc,true)
      simpa using congrArg Bool.not h'
    · have h' := congrFun h (i.succ,false)
      simpa using congrArg Bool.not h'
  · rintro ⟨h2,h3,rfl⟩
    funext i
    rcases i with ⟨j,b⟩
    cases b
    · induction j using Fin.cases <;> simp_all
    · induction j using Fin.lastCases <;> simp_all

lemma no_left_constant_right_opposite {m : ℕ} (hm : 2 ≤ m)
    (x : Fin 4 → Bool) (z : Edges m → Bool) (t : Bool)
    (hl : leftWord x z = fun _ => t) : ¬ Opposite (rightWord x z) := by
  obtain ⟨_,_,rfl⟩ := (left_constant x z t).1 hl
  intro h
  have h' := h (⟨1, by omega⟩ : Fin (m+1))
  have he₁ : (⟨1, by omega⟩ : Fin (m+1)) = (⟨1, by omega⟩ : Fin m).castSucc := rfl
  have he₂ : (⟨1, by omega⟩ : Fin (m+1)) = (⟨0, by omega⟩ : Fin m).succ := rfl
  rw [he₁, rightWord_castSucc_true, ← he₁, he₂, rightWord_succ_false] at h'
  cases t <;> simp at h'

lemma no_left_opposite_right_constant {m : ℕ} (hm : 0 < m)
    (x : Fin 4 → Bool) (z : Edges m → Bool) (t : Bool)
    (hr : rightWord x z = fun _ => t) : ¬ Opposite (leftWord x z) := by
  obtain ⟨_,_,rfl⟩ := (right_constant x z t).1 hr
  intro h
  have h' := ((left_opposite x _).1 h).2 ⟨0,hm⟩
  cases t <;> simp at h'

end Paper2.TransversalCube
