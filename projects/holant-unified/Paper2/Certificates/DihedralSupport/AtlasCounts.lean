import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! Typed labels for the projective atlas of Appendix A.1(i). Each two-block
label uses a strictly ordered pair; each triangle uses a strictly ordered
triple. The phase parameters are actual residues in F₃. Numerical counts are
derived from these finite types, with no stored accepted-case list. Geometry
and the projective pencil lift are separate theorems about these labels. -/
namespace Paper2.Certificates.DihedralSupport.AtlasCounts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 10000

abbrev Block := Fin 4
abbrev Phase := ZMod 3
abbrev Pair := {p : Block × Block // p.1 < p.2}
abbrev Triple := {t : Block × Block × Block // t.1 < t.2.1 ∧ t.2.1 < t.2.2}

abbrev SingleLabel := Block × Phase
abbrev TwoBlockLabel := Pair × Phase × Phase
abbrev PointLabel := SingleLabel ⊕ TwoBlockLabel
abbrev OneBlockLabel := Block
abbrev RulingLabel := Pair × Bool × Phase
abbrev SecantLabel := Pair × Phase × Phase
abbrev TriangleLabel := Triple × (Fin 3 → Phase)
abbrev RichLabel := OneBlockLabel ⊕ (RulingLabel ⊕ (SecantLabel ⊕ TriangleLabel))
abbrev OrderedLabel := RichLabel × Equiv.Perm (Fin 3)

instance : DecidableEq (Fin 3 → Phase) := Fintype.decidablePiFintype
instance : BEq PointLabel := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq PointLabel where
  eq_of_beq := of_decide_eq_true
  rfl := by intro a; exact decide_eq_true rfl
instance : BEq RichLabel := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq RichLabel where
  eq_of_beq := of_decide_eq_true
  rfl := by intro a; exact decide_eq_true rfl

def single (p : Block) (r : Phase) : PointLabel := .inl (p,r)
def twoBlock (p : Pair) (r t : Phase) : PointLabel := .inr (p,r,t)
def phase (j : Fin 3) : Phase := j.val

def lowerPair (t : Triple) : Pair := ⟨(t.1.1,t.1.2.1),t.2.1⟩
def outerPair (t : Triple) : Pair := ⟨(t.1.1,t.1.2.2),lt_trans t.2.1 t.2.2⟩
def upperPair (t : Triple) : Pair := ⟨(t.1.2.1,t.1.2.2),t.2.2⟩

/-- The three actual point labels of a rich line. For a ruling, `false`
fixes u=r+t and `true` fixes v=r−t; in both cases r runs through F₃. -/
def richPoints : RichLabel → Fin 3 → PointLabel
  | .inl p, j => single p (phase j)
  | .inr (.inl (p,b,c)), j =>
      twoBlock p (phase j) (if b then phase j - c else c - phase j)
  | .inr (.inr (.inl (p,r,t))), j =>
      ![single p.1.1 r,single p.1.2 t,twoBlock p r t] j
  | .inr (.inr (.inr (t,r))), j =>
      ![twoBlock (lowerPair t) (r 0) (r 1),
        twoBlock (outerPair t) (r 0) (r 2),
        twoBlock (upperPair t) (r 1) (r 2)] j

def richSet (r : RichLabel) : Finset PointLabel := Finset.univ.image (richPoints r)
def orderedPoints (r : OrderedLabel) : Fin 3 → PointLabel :=
  fun j => richPoints r.1 (r.2 j)

theorem pair_card : Fintype.card Pair = 6 := by decide +kernel
theorem triple_card : Fintype.card Triple = 4 := by decide +kernel
theorem phase_card : Fintype.card Phase = 3 := by decide +kernel
theorem single_card : Fintype.card SingleLabel = 12 := by
  rw [Fintype.card_prod,phase_card]
  norm_num
theorem twoBlock_card : Fintype.card TwoBlockLabel = 54 := by
  rw [Fintype.card_prod,Fintype.card_prod,pair_card,phase_card]
theorem point_card : Fintype.card PointLabel = 66 := by
  rw [Fintype.card_sum,single_card,twoBlock_card]
theorem oneBlock_card : Fintype.card OneBlockLabel = 4 := by decide +kernel
theorem ruling_card : Fintype.card RulingLabel = 36 := by
  rw [Fintype.card_prod,Fintype.card_prod,pair_card,phase_card]
  norm_num
theorem secant_card : Fintype.card SecantLabel = 54 := twoBlock_card
theorem triangle_card : Fintype.card TriangleLabel = 108 := by
  rw [Fintype.card_prod,Fintype.card_fun,triple_card,phase_card]
  norm_num
theorem rich_card : Fintype.card RichLabel = 202 := by
  rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_sum,
    oneBlock_card,ruling_card,secant_card,triangle_card]
theorem phaseAssignment_card : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Fintype.card_perm]
  norm_num
theorem ordered_card : Fintype.card OrderedLabel = 1212 := by
  rw [Fintype.card_prod,rich_card,phaseAssignment_card]

/-- Formulaic lexicographic enumeration: blocks, then ordered block pairs;
within each block choice phases run through representatives 0,1,2. -/
def phaseList : List Phase := (List.finRange 3).map phase
def pairList : List Pair := (List.finRange 4).flatMap fun p =>
  (List.finRange 4).filterMap fun q => if h : p < q then some ⟨(p,q),h⟩ else none
def pointList : List PointLabel :=
  ((List.finRange 4).flatMap fun p => phaseList.map (single p)) ++
  (pairList.flatMap fun p => phaseList.flatMap fun r => phaseList.map (twoBlock p r))

theorem pointList_length : pointList.length = 66 := by decide +kernel
theorem pointList_nodup : pointList.Nodup := by decide +kernel
theorem pointList_complete : ∀ p : PointLabel, p ∈ pointList := by
  have h : ∀ p ∈ (Finset.univ : Finset PointLabel), p ∈ pointList := by decide +kernel
  exact fun p => h p (Finset.mem_univ p)

theorem richPoints_distinct : ∀ r : RichLabel, Function.Injective (richPoints r) := by
  have h : ∀ r ∈ (Finset.univ : Finset RichLabel),
      ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      richPoints r i = richPoints r j → i = j := by decide +kernel
  exact fun r i j hij => h r (Finset.mem_univ r) i (Finset.mem_univ i)
    j (Finset.mem_univ j) hij
theorem richSet_card (r : RichLabel) : (richSet r).card = 3 := by
  rw [richSet,Finset.card_image_of_injective _ (richPoints_distinct r)]
  simp

def tripleList : List Triple := (List.finRange 4).flatMap fun p =>
  (List.finRange 4).flatMap fun q =>
    (List.finRange 4).filterMap fun r =>
      if h : p < q ∧ q < r then some ⟨(p,q,r),h⟩ else none
def phaseTripleList : List (Fin 3 → Phase) := phaseList.flatMap fun r =>
  phaseList.flatMap fun s => phaseList.map fun t => ![r,s,t]

/-- Formulaic lexicographic enumeration of the four geometric label classes. -/
def richList : List RichLabel :=
  (List.finRange 4).map Sum.inl ++
  (pairList.flatMap fun p => [false,true].flatMap fun b =>
    phaseList.map fun c => Sum.inr (Sum.inl (p,b,c))) ++
  (pairList.flatMap fun p => phaseList.flatMap fun r =>
    phaseList.map fun t => Sum.inr (Sum.inr (Sum.inl (p,r,t)))) ++
  (tripleList.flatMap fun t => phaseTripleList.map fun r =>
    Sum.inr (Sum.inr (Sum.inr (t,r))))

theorem richList_length : richList.length = 202 := by decide +kernel
theorem richList_nodup : richList.Nodup := by decide +kernel
theorem richList_complete : ∀ r : RichLabel, r ∈ richList := by
  have he : richList.toFinset = Finset.univ := Finset.eq_univ_of_card richList.toFinset (by
    rw [List.toFinset_card_of_nodup richList_nodup,richList_length,rich_card])
  intro r
  apply List.mem_toFinset.mp
  rw [he]
  exact Finset.mem_univ r

end Paper2.Certificates.DihedralSupport.AtlasCounts

