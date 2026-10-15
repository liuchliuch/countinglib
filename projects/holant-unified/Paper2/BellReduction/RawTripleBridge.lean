import Paper2.BellReduction.UniqueRows
import Paper2.Complexity.BellMachines.RawTriple

/-! The total raw-row machine implementation agrees with ordered three-step
extraction on every valid instance. Positive-arity row uniqueness is proved
from the incidence permutation, with no simple/loopless graph restriction. -/
namespace Paper2.BellReduction
open Complexity RawOccurrence
namespace RawTripleBridge

def marked (vs : List RawVertex) := vs.filter (fun v => v.1 == 0)

theorem marked_nodup {G : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hzero : arity 0 = 2) : (marked G.vertices).Nodup := by
  apply List.pairwise_filter.mpr
  apply List.pairwise_iff_get.mpr
  intro i j hij hi hj heq
  have hz : (G.vertices.get i).1 = 0 := by simpa using hi
  have he := marked_binary_row_unique hG hzero i j hz heq
  exact (ne_of_lt hij) he

theorem popMarked_marked {vs : List RawVertex} {p : List RawEndpoint} {rest : List RawVertex}
    (h : popMarked vs = some (p,rest)) : marked vs = (0,p)::marked rest := by
  induction vs generalizing rest with
  | nil => simp [popMarked] at h
  | cons v vs ih =>
    rcases v with ⟨a,q⟩
    by_cases ha : a = 0
    · subst a
      simp only [popMarked,ite_true,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      simp [marked]
    · cases hp : popMarked vs with
      | none => simp [popMarked,ha,hp] at h
      | some r =>
        rcases r with ⟨r,tail⟩
        simp only [popMarked,ha,ite_false,hp,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simpa [marked,ha] using ih hp

theorem popMarked_nodup {vs : List RawVertex} {p : List RawEndpoint} {rest : List RawVertex}
    (h : popMarked vs = some (p,rest)) (hn : (marked vs).Nodup) :
    (marked rest).Nodup := by
  rw [popMarked_marked h] at hn
  exact hn.of_cons

theorem popMarked_filter {vs : List RawVertex} {p : List RawEndpoint} {rest : List RawVertex}
    (h : popMarked vs = some (p,rest)) (hn : (marked vs).Nodup) :
    rest = vs.filter (fun v => v != (0,p)) := by
  induction vs generalizing rest with
  | nil => simp [popMarked] at h
  | cons v vs ih =>
    rcases v with ⟨a,q⟩
    by_cases ha : a = 0
    · subst a
      simp only [popMarked,ite_true,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hnot : (0,q) ∉ vs := by
        intro hm
        have hh : (0,q) ∈ marked vs := by simp [marked,hm]
        exact (List.nodup_cons.mp (by simpa [marked] using hn)).1 hh
      simp only [List.filter_cons, bne_self_eq_false,Bool.false_eq_true,ite_false]
      symm
      apply List.filter_eq_self.mpr
      intro v hv
      simp only [bne_iff_ne]
      intro he
      exact hnot (he ▸ hv)
    · cases hp : popMarked vs with
      | none => simp [popMarked,ha,hp] at h
      | some r =>
        rcases r with ⟨r,tail⟩
        simp only [popMarked,ha,ite_false,hp,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        have hn' : (marked vs).Nodup := by simpa [marked,ha] using hn
        have hne : (a,q) ≠ (0,r) := by intro he; exact ha (congrArg Prod.fst he)
        simpa [hne] using congrArg (List.cons (a,q)) (ih hp hn')

/-- The total filter/select implementation agrees with the ordered extraction
on every input whose marked rows are unique. -/
theorem split_eq {G : RawClosedNetwork} {t : Split}
    (h : splitThree G.vertices = some t) (hn : (marked G.vertices).Nodup) :
    BellMachines.RawTriple.split G = t := by
  cases h₁ : popMarked G.vertices with
  | none => simp [splitThree,h₁] at h
  | some a =>
    cases h₂ : popMarked a.2 with
    | none => simp [splitThree,h₁,h₂] at h
    | some b =>
      cases h₃ : popMarked b.2 with
      | none => simp [splitThree,h₁,h₂,h₃] at h
      | some c =>
        simp [splitThree,h₁,h₂,h₃] at h
        subst t
        have ha := popMarked_marked h₁
        rw [popMarked_marked h₂,popMarked_marked h₃] at ha
        have hna := popMarked_nodup h₁ hn
        have hnb := popMarked_nodup h₂ hna
        have hs0 : BellMachines.RawTriple.selected G 0 = (0,a.1) := by
          change (marked G.vertices).getD 0 (0,[]) = _
          rw [ha]
          rfl
        have hs1 : BellMachines.RawTriple.selected G 1 = (0,b.1) := by
          change (marked G.vertices).getD 1 (0,[]) = _
          rw [ha]
          rfl
        have hs2 : BellMachines.RawTriple.selected G 2 = (0,c.1) := by
          change (marked G.vertices).getD 2 (0,[]) = _
          rw [ha]
          rfl
        have hr : BellMachines.RawTriple.rest G = c.2 := by
          unfold BellMachines.RawTriple.rest
          rw [hs0,hs1,hs2,popMarked_filter h₃ hnb,popMarked_filter h₂ hna,
            popMarked_filter h₁ hn]
          simp only [List.filter_filter]
          congr 1
          funext v
          unfold BellMachines.RawTriple.keep
          ac_rfl
        simp [BellMachines.RawTriple.split,hs0,hs1,hs2,hr]

/-- The literal machine output therefore inherits the kernel-checked real
instance validator and occurrence-count proofs from `RawOccurrence.perform`. -/
theorem splitThree_machine {G : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hzero : arity 0 = 2)
    (hc : 3 ≤ markedCount G.vertices) :
    splitThree G.vertices = some (BellMachines.RawTriple.split G) := by
  obtain ⟨t,ht⟩ := splitThree_exists hc
  rw [split_eq ht (marked_nodup hG hzero)]
  exact ht

theorem machine_wellFormed {G : RawClosedNetwork} {s : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s 1 arity) (hzero : arity 0 = 2)
    (hc : 3 ≤ markedCount G.vertices) (coreLabel : ℕ)
    (hl : coreLabel < s) (ha : arity coreLabel = 8) :
    (BellMachines.RawTriple.transform coreLabel G).WellFormed s 1 arity :=
  perform_wellFormed G coreLabel _ hG (splitThree_machine hG hzero hc) hzero hl ha

end RawTripleBridge
end Paper2.BellReduction
