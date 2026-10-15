import Paper2.RelativeEO.TaggedExtension
import Mathlib.Data.List.Perm.Basic

/-! Executable surgery on the actual serialized graph. Label zero designates
Bell occurrences, independently of semantic table equality. Three occurrences
are removed, their six ordered old endpoints are retained at one new RM8 vertex,
and one new Bell vertex is joined through two fresh native-X edges. -/
namespace Paper2.BellReduction.RawOccurrence
open Complexity

abbrev Row := RawVertex
abbrev End := RawEndpoint

def markedCount (vs : List Row) : ℕ := (vs.filter (fun v => v.1 == 0)).length

/-- Extract the first designated occurrence, retaining all other rows in order. -/
def popMarked : List Row → Option (List End × List Row)
  | [] => none
  | (a,p)::vs => if a = 0 then some (p,vs) else
      (popMarked vs).map (fun q => (q.1,(a,p)::q.2))

theorem popMarked_perm {vs : List Row} {p : List End} {rest : List Row}
    (h : popMarked vs = some (p,rest)) : vs.Perm ((0,p)::rest) := by
  induction vs generalizing rest with
  | nil => simp [popMarked] at h
  | cons v vs ih =>
    rcases v with ⟨a,q⟩
    by_cases ha : a = 0
    · subst a
      simp only [popMarked,ite_true,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rfl
    · cases hp : popMarked vs with
      | none => simp [popMarked,ha,hp] at h
      | some r =>
        rcases r with ⟨r,tail⟩
        simp only [popMarked,ha,ite_false,hp,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact (List.Perm.cons _ (ih hp)).trans (List.Perm.swap _ _ _)

theorem markedCount_perm {vs ws : List Row} (h : vs.Perm ws) :
    markedCount vs = markedCount ws :=
  (h.filter (fun v : Row => v.1 == 0)).length_eq

@[simp] theorem markedCount_cons_zero (p : List End) (vs : List Row) :
    markedCount ((0,p)::vs) = markedCount vs + 1 := by
  simp [markedCount]

theorem popMarked_count {vs : List Row} {p : List End} {rest : List Row}
    (h : popMarked vs = some (p,rest)) : markedCount vs = markedCount rest + 1 := by
  rw [markedCount_perm (popMarked_perm h),markedCount_cons_zero]

theorem popMarked_none (vs : List Row) : popMarked vs = none ↔ markedCount vs = 0 := by
  induction vs with
  | nil => simp [popMarked,markedCount]
  | cons v vs ih =>
    rcases v with ⟨a,p⟩
    by_cases ha : a = 0
    · subst a
      simp [popMarked,markedCount]
    · simp [popMarked,markedCount,ha] at *
      exact ih

theorem popMarked_exists {vs : List Row} (h : 0 < markedCount vs) :
    ∃ p rest, popMarked vs = some (p,rest) := by
  cases hp : popMarked vs with
  | none => have hh := (popMarked_none vs).mp hp; omega
  | some p => exact ⟨p.1,p.2,rfl⟩

structure Split where
  first : List End
  second : List End
  third : List End
  rest : List Row
  deriving DecidableEq

def splitThree (vs : List Row) : Option Split := do
  let a ← popMarked vs
  let b ← popMarked a.2
  let c ← popMarked b.2
  pure ⟨a.1,b.1,c.1,c.2⟩

theorem splitThree_perm {vs : List Row} {s : Split} (h : splitThree vs = some s) :
    vs.Perm ((0,s.first)::(0,s.second)::(0,s.third)::s.rest) := by
  cases h₁ : popMarked vs with
  | none => simp [splitThree,h₁] at h
  | some a =>
    cases h₂ : popMarked a.2 with
    | none => simp [splitThree,h₁,h₂] at h
    | some b =>
      cases h₃ : popMarked b.2 with
      | none => simp [splitThree,h₁,h₂,h₃] at h
      | some c =>
        simp [splitThree,h₁,h₂,h₃] at h
        subst s
        exact (popMarked_perm h₁).trans
          ((List.Perm.cons _ (popMarked_perm h₂)).trans
            (List.Perm.cons _ (List.Perm.cons _ (popMarked_perm h₃))))

theorem splitThree_count {vs : List Row} {s : Split} (h : splitThree vs = some s) :
    markedCount vs = markedCount s.rest + 3 := by
  rw [markedCount_perm (splitThree_perm h)]
  simp only [markedCount_cons_zero]

theorem splitThree_length {vs : List Row} {s : Split} (h : splitThree vs = some s) :
    vs.length = s.rest.length + 3 := by
  have hh := (splitThree_perm h).length_eq
  simp only [List.length_cons] at hh
  omega

theorem splitThree_exists {vs : List Row} (h : 3 ≤ markedCount vs) :
    ∃ s, splitThree vs = some s := by
  obtain ⟨p,a,h₁⟩ := popMarked_exists (vs := vs) (by omega)
  have hc₁ := popMarked_count h₁
  obtain ⟨q,b,h₂⟩ := popMarked_exists (vs := a) (by omega)
  have hc₂ := popMarked_count h₂
  obtain ⟨r,c,h₃⟩ := popMarked_exists (vs := b) (by omega)
  exact ⟨⟨p,q,r,c⟩,by simp [splitThree,h₁,h₂,h₃]⟩

/-- Old endpoints remain ordered within each marked binary; no old edge is
removed or reoriented, even when selected occurrences meet or have self-loops. -/
def perform (G : RawClosedNetwork) (coreLabel : ℕ) (s : Split) : RawClosedNetwork where
  vertices := s.rest ++ [
    (coreLabel, [(G.edges.length,false),(G.edges.length+1,false)] ++ s.first ++ s.second ++ s.third),
    (0, [(G.edges.length,true),(G.edges.length+1,true)])]
  edges := G.edges ++ [0,0]

/-- The executable one-step transformation is defined exactly when three
marked rows can be extracted. -/
def step (G : RawClosedNetwork) (coreLabel : ℕ) : Option RawClosedNetwork :=
  (splitThree G.vertices).map (perform G coreLabel)

theorem perform_edges (G : RawClosedNetwork) (coreLabel : ℕ) (s : Split) :
    (perform G coreLabel s).edges.length = G.edges.length + 2 := by simp [perform]

theorem perform_vertices (G : RawClosedNetwork) (coreLabel : ℕ) (s : Split)
    (h : splitThree G.vertices = some s) :
    (perform G coreLabel s).vertices.length + 1 = G.vertices.length := by
  have hh := splitThree_length h
  simp only [perform,List.length_append,List.length_cons,List.length_nil]
  omega

theorem perform_count (G : RawClosedNetwork) (coreLabel : ℕ) (s : Split)
    (hc : coreLabel ≠ 0) (h : splitThree G.vertices = some s) :
    markedCount (perform G coreLabel s).vertices + 2 = markedCount G.vertices := by
  have hh := splitThree_count h
  simp [perform,markedCount,List.filter_append,hc] at *
  omega

private theorem vertex_valid_mem {G : RawClosedNetwork} {s : ℕ} {arity : ℕ → ℕ}
    (h : G.WellFormed s 1 arity) {v : Row} (hv : v ∈ G.vertices) :
    v.1 < s ∧ v.2.length = arity v.1 := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hv
  rw [← hi]
  exact h.1 i

private theorem edge_valid_mem {G : RawClosedNetwork} {s : ℕ} {arity : ℕ → ℕ}
    (h : G.WellFormed s 1 arity) {e : ℕ} (he : e ∈ G.edges) : e < 1 := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
  rw [← hi]
  exact h.2.1 i

/-- The expected edge-end list gains precisely the two new labelled pairs. -/
theorem perform_expected (G : RawClosedNetwork) (coreLabel : ℕ) (t : Split) :
    (perform G coreLabel t).expectedEndpoints = G.expectedEndpoints ++
      [(G.edges.length,false),(G.edges.length,true),
        (G.edges.length+1,false),(G.edges.length+1,true)] := by
  unfold RawClosedNetwork.expectedEndpoints
  rw [perform_edges,List.ofFn_add,List.flatten_append]
  simp [List.ofFn_succ]

/-- The actual endpoint permutation survives the surgery, including all
selected self-loops, interconnections, parallel edges and closed components. -/
theorem perform_endpoint_perm (G : RawClosedNetwork) (coreLabel : ℕ) (t : Split)
    (hs : splitThree G.vertices = some t)
    (hE : G.endpoints.Perm G.expectedEndpoints) :
    (perform G coreLabel t).endpoints.Perm (perform G coreLabel t).expectedEndpoints := by
  have hp := (splitThree_perm hs).map Prod.snd
  have hf := hp.flatten
  have ho : G.endpoints.Perm (t.first ++ t.second ++ t.third ++
      (t.rest.map Prod.snd).flatten) := by
    simpa [RawClosedNetwork.endpoints,List.append_assoc] using hf
  apply List.perm_iff_count.mpr
  intro e
  have hc := (ho.symm.trans hE).count_eq e
  rw [perform_expected]
  simp only [perform,RawClosedNetwork.endpoints,List.map_append,List.map_cons,List.map_nil,
    List.flatten_append,List.flatten_cons,List.flatten_nil,List.count_append,List.count_cons,
    List.count_nil] at *
  omega

/-- This concrete raw graph always passes the real instance validator when the
original input does. The source's two binary arities and the chosen core arity
are actual label lookups, not informal promises about a graph picture. -/
theorem perform_wellFormed (G : RawClosedNetwork) (coreLabel : ℕ) (t : Split)
    {signatureCount : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed signatureCount 1 arity)
    (hs : splitThree G.vertices = some t)
    (hzero : arity 0 = 2) (hc : coreLabel < signatureCount) (hcore : arity coreLabel = 8) :
    (perform G coreLabel t).WellFormed signatureCount 1 arity := by
  have hp := splitThree_perm hs
  have h₀ : (0,t.first) ∈ G.vertices := hp.mem_iff.mpr (by simp)
  have h₁ : (0,t.second) ∈ G.vertices := hp.mem_iff.mpr (by simp)
  have h₂ : (0,t.third) ∈ G.vertices := hp.mem_iff.mpr (by simp)
  have hf := vertex_valid_mem hG h₀
  have hg := vertex_valid_mem hG h₁
  have hh := vertex_valid_mem hG h₂
  have hlen : t.first.length = 2 ∧ t.second.length = 2 ∧ t.third.length = 2 := by
    simpa only [hzero] using And.intro hf.2 (And.intro hg.2 hh.2)
  refine ⟨?_,?_,perform_endpoint_perm G coreLabel t hs hG.2.2⟩
  · intro i
    have hi := List.get_mem (perform G coreLabel t).vertices i
    change (perform G coreLabel t).vertices.get i ∈
      t.rest ++ [(coreLabel, _),(0,_)] at hi
    rcases List.mem_append.mp hi with hrest | hnew
    · exact vertex_valid_mem hG (hp.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hrest))))
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hnew
      rcases hnew with he | he
      · rw [he]
        simp [hlen.1,hlen.2.1,hlen.2.2,hcore,hc]
      · rw [he]
        simp [hzero,hf.1]
  · intro i
    have hi := List.get_mem (perform G coreLabel t).edges i
    change _ ∈ G.edges ++ [0,0] at hi
    rcases List.mem_append.mp hi with hold | hnew
    · exact edge_valid_mem hG hold
    · simp only [List.mem_cons,List.mem_nil_iff,or_false,or_self] at hnew
      rw [hnew]
      decide

end Paper2.BellReduction.RawOccurrence
