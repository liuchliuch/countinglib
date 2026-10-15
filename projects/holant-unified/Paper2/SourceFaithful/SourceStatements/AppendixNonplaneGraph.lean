import Paper2.Certificates.Q8Support
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The literal nonplane exchange graph of Proposition A.10. Its connectedness
uses the existing checked Q8 spanning tree, and its odd cycle is the source's
three concrete masks. No reachability search is used in the graph proof. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.SourceStatements.AppendixNonplaneGraph
open Paper2.ReedMuller
open Paper2.Certificates

def Nonplane := {x : Word // weight x = 4 ∧ supportXor x ≠ (fun _ => false)}

def Exchange (x y : Word) : Prop :=
  ∃ p q : Fin 8, x p = true ∧ x q = false ∧ y = Q8.swap x p q

private theorem exchange_distinct (x : Word) (p q : Fin 8)
    (hp : x p = true) (hq : x q = false) : p ≠ q := by
  intro h
  subst q
  rw [hp] at hq
  cases hq

private theorem swap_reverse (x : Word) (p q : Fin 8)
    (hp : x p = true) (hq : x q = false) : Q8.swap (Q8.swap x p q) q p = x := by
  have hpq := exchange_distinct x p q hp hq
  funext t
  by_cases htp : t = p
  · subst t
    simp [Q8.swap,hpq,hp]
  by_cases htq : t = q
  · subst t
    simp [Q8.swap,hq]
  simp [Q8.swap,htp,htq]

theorem exchange_symm {x y : Word} (h : Exchange x y) : Exchange y x := by
  obtain ⟨p,q,hp,hq,rfl⟩ := h
  have hpq := exchange_distinct x p q hp hq
  refine ⟨q,p,?_,?_,?_⟩
  · simp [Q8.swap,Ne.symm hpq]
  · simp [Q8.swap]
  · exact (swap_reverse x p q hp hq).symm

private theorem exchange_irrefl (x : Word) : ¬ Exchange x x := by
  rintro ⟨p,q,hp,hq,hx⟩
  have h := congrFun hx p
  simp [Q8.swap,hp] at h

def G : SimpleGraph Nonplane where
  Adj x y := Exchange x.val y.val
  symm := ⟨fun _ _ h => exchange_symm h⟩
  loopless := ⟨fun x => exchange_irrefl x.val⟩

theorem adj_iff (x y : Nonplane) : G.Adj x y ↔
    ∃ p q : Fin 8, x.val p = true ∧ x.val q = false ∧ y.val = Q8.swap x.val p q := Iff.rfl

theorem adj_of_badSwap (x y : Nonplane) (p q : Fin 8)
    (h : Q8.BadSwap x.val y.val p q) : G.Adj x y := by
  obtain ⟨_,hp,hq,hs,_,_⟩ := h
  exact ⟨p,q,hp,hq,hs⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Validity of the 56 stored vertex masks. This checks the certificate's
vertex data only; all reachability below follows from its parent tree. -/
theorem nonplane_valid (i : Fin 56) :
    weight (Q8.nonplane i) = 4 ∧ supportXor (Q8.nonplane i) ≠ (fun _ => false) := by
  revert i
  decide +kernel

def vertex (i : Fin 56) : Nonplane := ⟨Q8.nonplane i,nonplane_valid i⟩

theorem vertex_coverage (x : Nonplane) : ∃ i : Fin 56, x = vertex i := by
  obtain ⟨i,hi⟩ := Q8.nonplane_coverage x.val x.property.1 x.property.2
  exact ⟨i,Subtype.ext hi⟩

theorem tree_adj (i : Fin 56) (hi : i.val ≠ 0) :
    G.Adj (vertex (Q8.tree i).1) (vertex i) :=
  adj_of_badSwap _ _ _ _ (Q8.tree_valid i hi).2

/-- Every stored vertex has an actual graph walk from the root, by strong
induction on its strictly decreasing certified parent index. -/
theorem root_reachable (i : Fin 56) : G.Reachable (vertex 0) (vertex i) := by
  have all_reachable : ∀ m (hm : m < 56), G.Reachable (vertex 0) (vertex ⟨m,hm⟩) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases hm0 : m = 0
      · subst m
        exact SimpleGraph.Reachable.rfl
      · have ht := Q8.tree_valid ⟨m,hm⟩ hm0
        have hp := ih (Q8.tree ⟨m,hm⟩).1.val ht.1 (Q8.tree ⟨m,hm⟩).1.isLt
        exact hp.trans (tree_adj ⟨m,hm⟩ hm0).reachable
  exact all_reachable i.val i.isLt

theorem connected : G.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨vertex 0,?_⟩
  intro x
  obtain ⟨i,rfl⟩ := vertex_coverage x
  exact root_reachable i

def triangle0 : Nonplane := vertex 0
def triangle1 : Nonplane := vertex 10
def triangle2 : Nonplane := vertex 5

@[simp] theorem triangle0_word : triangle0.val = Q8.fromMask 23 := rfl
@[simp] theorem triangle1_word : triangle1.val = Q8.fromMask 39 := rfl
@[simp] theorem triangle2_word : triangle2.val = Q8.fromMask 53 := rfl

theorem triangle_adj : G.Adj triangle0 triangle1 ∧
    G.Adj triangle1 triangle2 ∧ G.Adj triangle2 triangle0 := by
  exact ⟨adj_of_badSwap _ _ 4 5 Q8.odd_triangle.1,
    adj_of_badSwap _ _ 1 4 Q8.odd_triangle.2.1,
    adj_of_badSwap _ _ 5 1 Q8.odd_triangle.2.2⟩

theorem triangle : triangle0 ≠ triangle1 ∧ triangle1 ≠ triangle2 ∧ triangle2 ≠ triangle0 ∧
    G.Adj triangle0 triangle1 ∧ G.Adj triangle1 triangle2 ∧ G.Adj triangle2 triangle0 :=
  ⟨triangle_adj.1.ne,triangle_adj.2.1.ne,triangle_adj.2.2.ne,
    triangle_adj.1,triangle_adj.2.1,triangle_adj.2.2⟩

def triangleWalk : G.Walk triangle0 triangle0 :=
  .cons triangle_adj.1 (.cons triangle_adj.2.1 (.cons triangle_adj.2.2 .nil))

theorem triangleWalk_length : triangleWalk.length = 3 := rfl

theorem triangleWalk_isCycle : triangleWalk.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · simp [triangleWalk,SimpleGraph.Walk.isPath_def,
      triangle_adj.2.1.ne,triangle_adj.2.2.ne,triangle_adj.1.ne']
  · rw [triangleWalk_length]

theorem exists_odd_cycle : ∃ w : G.Walk triangle0 triangle0, w.IsCycle ∧ Odd w.length :=
  ⟨triangleWalk,triangleWalk_isCycle,by rw [triangleWalk_length]; decide⟩

theorem exists_triangle_cycle : ∃ v : Nonplane, ∃ w : G.Walk v v,
    w.IsCycle ∧ w.length = 3 :=
  ⟨triangle0,triangleWalk,triangleWalk_isCycle,triangleWalk_length⟩

end Paper2.SourceFaithful.SourceStatements.AppendixNonplaneGraph

