import Paper2.Paper1ProvedPinPairLoop
import Paper2.Charge

/-! Exact support and Hamming-gap identities for the pin/loop descent in the
odd theorem. The X-loop exit retains both selected entries only when their
competing contributions vanish. Every possible competing nonzero entry is
instead consumed by a genuine fixed-pair cap. -/
namespace Paper2.Paper1Proved.OddUnary.TwoWordDescent
open Paper2
open Paper2.Paper1Proved
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {n : ℕ}

def gap {m : ℕ} (x y : Fin m → Bool) : ℤ := (weight y : ℤ)-(weight x : ℤ)

/-- A positive lower bound for every positive occupied Hamming-weight gap. -/
def MinimumGap {m : ℕ} (f : Signature K m) (d : ℕ) : Prop :=
  ∀ x y, f x ≠ 0 → f y ≠ 0 → 0 < gap x y → (d : ℤ) ≤ gap x y

theorem weight_insert (i : Fin (n+1)) (b : Bool) (x : Fin n → Bool) :
    weight (Fin.insertNth i b x)=(if b then 1 else 0)+weight x := by
  have he : (fun j : Fin (n+1) => if (Fin.insertNth (α := fun _ => Bool) i b x j) then (1 : ℕ) else 0)=
      Fin.insertNth i (if b then 1 else 0) (fun j => if x j then 1 else 0) := by
    funext j
    induction j using i.succAboveCases <;> simp
  unfold weight
  rw [he,Fin.sum_insertNth]

theorem weight_remove (i : Fin (n+1)) (x : Fin (n+1) → Bool) :
    weight x=(if x i then 1 else 0)+weight (Fin.removeNth i x) := by
  have h := weight_insert i (x i) (Fin.removeNth i x)
  rw [Fin.insertNth_self_removeNth] at h
  exact h

theorem gap_insert (i : Fin (n+1)) (b : Bool) (x y : Fin n → Bool) :
    gap (Fin.insertNth i b x) (Fin.insertNth i b y)=gap x y := by
  simp only [gap,weight_insert,Nat.cast_add]
  omega

theorem agreeing_pin (f : Signature K (n+1)) (i : Fin (n+1))
    (x y : Fin (n+1) → Bool) (hx : f x ≠ 0) (hy : f y ≠ 0)
    (hi : x i=y i) :
    PinDeletion.pinCoordinate f i (x i) (Fin.removeNth i x) ≠ 0 ∧
      PinDeletion.pinCoordinate f i (x i) (Fin.removeNth i y) ≠ 0 ∧
      gap (Fin.removeNth i x) (Fin.removeNth i y)=gap x y := by
  have hy' : Fin.insertNth i (x i) (Fin.removeNth i y)=y := by
    rw [hi,Fin.insertNth_self_removeNth]
  refine ⟨by simpa [PinDeletion.pinCoordinate] using hx,
    by simpa only [PinDeletion.pinCoordinate,hy'] using hy,?_⟩
  have h := gap_insert i (x i) (Fin.removeNth i x) (Fin.removeNth i y)
  simpa only [Fin.insertNth_self_removeNth,hy'] using h.symm

theorem minimumGap_pin (f : Signature K (n+1)) (d : ℕ)
    (hd : MinimumGap f d) (i : Fin (n+1)) (b : Bool) :
    MinimumGap (PinDeletion.pinCoordinate f i b) d := by
  intro x y hx hy hxy
  have h := hd (Fin.insertNth i b x) (Fin.insertNth i b y) hx hy
  simpa only [gap_insert] using h (by simpa only [gap_insert] using hxy)

theorem weight_pairWord (i : Fin (n+2)) (j : Fin (n+1)) (b : Bool)
    (x : Fin n → Bool) : weight (PinPairLoop.pairWord i j b x)=weight x+1 := by
  unfold PinPairLoop.pairWord
  rw [weight_insert,weight_insert]
  cases b <;> simp <;> omega

theorem gap_pairWord (i : Fin (n+2)) (j : Fin (n+1)) (a b : Bool)
    (x y : Fin n → Bool) :
    gap (PinPairLoop.pairWord i j a x) (PinPairLoop.pairWord i j b y)=gap x y := by
  simp only [gap,weight_pairWord,Nat.cast_add]
  omega

theorem minimumGap_pairPin (f : Signature K (n+2)) (d : ℕ)
    (hd : MinimumGap f d) (i : Fin (n+2)) (j : Fin (n+1)) (a b : Bool) :
    MinimumGap (PinPairLoop.pairPin f i j a b) d :=
  minimumGap_pin (PinDeletion.pinCoordinate f i a) d (minimumGap_pin f d hd i a) j b

theorem minimumGap_pairLoop (f : Signature K (n+2)) (d : ℕ)
    (hd : MinimumGap f d) (i : Fin (n+2)) (j : Fin (n+1)) :
    MinimumGap (PinPairLoop.pairLoop f i j) d := by
  intro x y hx hy hxy
  have hx' : ∃ a : Bool, f (PinPairLoop.pairWord i j a x) ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by simp [PinPairLoop.pairLoop,h])
  have hy' : ∃ b : Bool, f (PinPairLoop.pairWord i j b y) ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (by simp [PinPairLoop.pairLoop,h])
  obtain ⟨a,ha⟩ := hx'
  obtain ⟨b,hb⟩ := hy'
  have h := hd (PinPairLoop.pairWord i j a x) (PinPairLoop.pairWord i j b y) ha hb
  simpa only [gap_pairWord] using h (by simpa only [gap_pairWord] using hxy)

/-- Competing summands never disappear by assumption: a nonzero competing
summand yields a two-pin branch, and only the zero/zero branch uses the loop. -/
theorem pair_step (f : Signature K (n+2)) (i : Fin (n+2)) (j : Fin (n+1))
    (b : Bool) (x y : Fin n → Bool)
    (hx : f (PinPairLoop.pairWord i j b x) ≠ 0)
    (hy : f (PinPairLoop.pairWord i j (!b) y) ≠ 0) :
    (∃ a : Bool, PinPairLoop.pairPin f i j a (!a) x ≠ 0 ∧
      PinPairLoop.pairPin f i j a (!a) y ≠ 0) ∨
      (PinPairLoop.pairLoop f i j x ≠ 0 ∧ PinPairLoop.pairLoop f i j y ≠ 0) := by
  by_cases hxy : f (PinPairLoop.pairWord i j b y)=0
  · by_cases hyx : f (PinPairLoop.pairWord i j (!b) x)=0
    · right
      cases b <;> simp_all [PinPairLoop.pairLoop]
    · left
      exact ⟨!b,hyx,hy⟩
  · left
    exact ⟨b,hx,hxy⟩

theorem pairWord_remove (i : Fin (n+2)) (j : Fin (n+1))
    (x : Fin (n+2) → Bool) (h : x (i.succAbove j)=!(x i)) :
    PinPairLoop.pairWord i j (x i) (Fin.removeNth j (Fin.removeNth i x))=x := by
  unfold PinPairLoop.pairWord
  have hj : Fin.removeNth i x j=!(x i) := h
  rw [← hj,Fin.insertNth_self_removeNth,Fin.insertNth_self_removeNth]

theorem pair_gap_remove (i : Fin (n+2)) (j : Fin (n+1))
    (x y : Fin (n+2) → Bool)
    (hx : x (i.succAbove j)=!(x i)) (hy : y (i.succAbove j)=!(y i)) :
    gap (Fin.removeNth j (Fin.removeNth i x))
      (Fin.removeNth j (Fin.removeNth i y))=gap x y := by
  have h := gap_pairWord i j (x i) (y i)
    (Fin.removeNth j (Fin.removeNth i x)) (Fin.removeNth j (Fin.removeNth i y))
  rw [pairWord_remove i j x hx,pairWord_remove i j y hy] at h
  exact h.symm

end
end Paper2.Paper1Proved.OddUnary.TwoWordDescent
