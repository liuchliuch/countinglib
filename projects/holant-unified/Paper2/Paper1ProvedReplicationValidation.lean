import Paper2.Paper1ProvedReplicationCompiler
import Paper2.Paper1ProvedReplicationOrdinals

/-! Literal incidence and occurrence validation for the generic carrier chain. -/
noncomputable section
namespace Paper2.Paper1Proved.ReplicationCompiler
open Holant.Complexity Holant.Complexity.RawClosedNetwork
open Holant.Complexity.FixedGadgetSubstitution
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
variable (D : Data)

def block (m t : ℕ) (side : Bool) : List RawEndpoint :=
  (List.finRange D.gArity).map
    (fun i => (m+D.closure.edges.length+D.gArity*t+i.val,side))
def pending (m k t : ℕ) : List RawEndpoint :=
  if t=k then D.seedPorts.map (shift m) else block D m t false

theorem block_both (m t : ℕ) :
    (block D m t false ++ block D m t true).Perm
      (edgeEnds (m+D.closure.edges.length+D.gArity*t) D.gArity) := by
  have h := List.flatMap_append_perm (List.finRange D.gArity)
    (fun i => [(m+D.closure.edges.length+D.gArity*t+i.val,false)])
    (fun i => [(m+D.closure.edges.length+D.gArity*t+i.val,true)])
  have he : (List.finRange D.gArity).map Fin.val=List.range D.gArity := by
    apply List.ext_getElem <;> simp
  rw [edgeEnds,← he,List.flatMap_map]
  simpa [block,List.map_eq_flatMap,Function.comp_def] using h

theorem count_cons (row : RawVertex) (rows : List RawVertex) :
    count (row::rows)=(if row.1=0 then 1 else 0)+count rows := by
  by_cases h : row.1=0 <;> simp [count,h,Nat.add_comm]

theorem unique_seed (rows : List RawVertex) (h : count rows=1) :
    ∃ seed : Fin rows.length, (rows.get seed).1=0 ∧
      RawGrouping.selected 0 rows=(rows.get seed).2 := by
  obtain ⟨row,he⟩ := List.length_eq_one_iff.mp h
  have hm : row ∈ rows.filter (fun row => row.1==0) := by rw [he]; simp
  have hr := List.mem_filter.mp hm
  obtain ⟨seed,hs⟩ := List.mem_iff_get.mp hr.1
  refine ⟨seed,?_,?_⟩
  · change (rows.get seed).1=0
    rw [hs]
    simpa using hr.2
  · change RawGrouping.selected 0 rows=(rows.get seed).2
    rw [hs]
    simp [RawGrouping.selected,he]

def closureEnds (m k : ℕ) (rows : List RawVertex) : List RawEndpoint :=
  (rows.map (closureRow D m k)).flatMap Prod.snd

theorem closure_ends_split (m k : ℕ) (rows : List RawVertex) :
    (closureEnds D m k rows).Perm
      (((RawGrouping.keep 0 rows).flatMap Prod.snd).map (shift m) ++
        (rows.filter (fun row => row.1==0)).flatMap
          (fun row => if k=0 then row.2.map (shift m) else block D m 0 false)) := by
  induction rows with
  | nil => simp [closureEnds,RawGrouping.keep]
  | cons row rows ih =>
    apply List.perm_iff_count.mpr
    intro p
    have hi := ih.count_eq p
    by_cases hz : row.1=0 <;> by_cases hk : k=0 <;>
      simp [closureEnds,closureRow,RawGrouping.keep,hz,hk,block,List.count_append] at hi ⊢ <;> omega

theorem closure_ends (m k : ℕ) (hc : count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts) :
    (closureEnds D m k D.closure.vertices).Perm
      (((RawGrouping.keep 0 D.closure.vertices).flatMap Prod.snd).map (shift m) ++ pending D m k 0) := by
  obtain ⟨row,he⟩ := List.length_eq_one_iff.mp hc
  have hp := closure_ends_split D m k D.closure.vertices
  have hh : row.2=D.seedPorts := by simpa [RawGrouping.selected,he] using hs
  simpa [he,hh,pending,block,eq_comm] using hp

theorem closure_original_ends (m : ℕ)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts) :
    (D.closure.endpoints.map (shift m)).Perm
      (((RawGrouping.keep 0 D.closure.vertices).flatMap Prod.snd).map (shift m) ++
        D.seedPorts.map (shift m)) := by
  have h := (RawGrouping.split_endpoints 0 D.closure.vertices).map (shift m)
  simpa [RawClosedNetwork.endpoints,List.flatMap,hs] using h

theorem seed_enumeration (m : ℕ) (hs : D.seedPorts.length=D.gArity) :
    (List.finRange D.gArity).map (fun i => shift m (D.seedPorts.getD i.val (0,false))) =
      D.seedPorts.map (shift m) := by
  apply List.ext_getElem
  · simp [hs]
  · intro i h₁ h₂
    simp only [List.length_map,List.length_finRange] at h₁
    have hi : i<D.seedPorts.length := by omega
    simp [List.getD_eq_getElem,hi]

theorem marked_row_ports (m k t : ℕ) (row : RawVertex) (hz : row.1=0)
    (hs : D.seedPorts.length=D.gArity) :
    (sourceRow D m k t row).2=block D m t true ++ (pending D m k (t+1) ++ row.2) := by
  by_cases ht : t+1=k
  · simp only [sourceRow,if_pos hz,carrierP,ht,↓reduceIte,pending]
    rw [seed_enumeration D m hs]
    rfl
  · simp [sourceRow,hz,block,carrierA,carrierP,pending,ht]

theorem added_edges (rows : List RawVertex) :
    rows.flatMap (fun row => if row.1=0 then List.replicate D.gArity 0 else []) =
      List.replicate (D.gArity*count rows) 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases hz : row.1=0 <;>
      simp [List.flatMap_cons,hz,count_cons,ih,Nat.mul_add,List.replicate_add, -List.replicate_append_replicate]

theorem query_edge_length (x : Input D) :
    (query D x).edges.length=x.val.edges.length+D.closure.edges.length+D.gArity*count x.val.vertices := by
  simp [query,added_edges,Nat.add_assoc]


abbrev emittedRows (m k t : ℕ) (rows : List RawVertex) : List RawVertex :=
  ReplicationOrdinals.expand (fun row : RawVertex => row.1==0) (sourceRow D m k) t rows

theorem before_eq_count (x : RowQuery D) :
    before D x=count (x.1.val.vertices.take x.2.val) := by
  exact Holant.Complexity.FixedGadgetSubstitution.Compiler.indicator_sum 0 _

theorem query_vertices (x : Input D) :
    (query D x).vertices=D.closure.vertices.map (closureRow D x.val.edges.length (count x.val.vertices)) ++
      emittedRows D x.val.edges.length (count x.val.vertices) 0 x.val.vertices := by
  rw [emittedRows,ReplicationOrdinals.expand_eq_indexed]
  dsimp only [query]
  congr 1
  apply List.map_congr_left
  intro v _
  rw [Nat.zero_add,before_eq_count D ⟨x,v⟩]
  rfl

theorem emitted_partition (m k t : ℕ) (rows : List RawVertex)
    (ht : t+count rows=k) (hs : D.seedPorts.length=D.gArity) :
    (pending D m k t ++ (emittedRows D m k t rows).flatMap Prod.snd).Perm
      (rows.flatMap Prod.snd ++ pending D m k k ++
        edgeEnds (m+D.closure.edges.length+D.gArity*t) (D.gArity*count rows)) := by
  induction rows generalizing t with
  | nil =>
    have htk : t=k := by simpa [count] using ht
    simp [emittedRows,ReplicationOrdinals.expand,pending,count,htk]
  | cons row rows ih =>
    by_cases hz : row.1=0
    · have htk : t≠k := by rw [count_cons,if_pos hz] at ht; omega
      have hn : (t+1)+count rows=k := by rw [count_cons,if_pos hz] at ht; omega
      have hi := ih (t+1) hn
      apply List.perm_iff_count.mpr
      intro p
      have hic := hi.count_eq p
      have hb := (block_both D m t).count_eq p
      have hr := marked_row_ports D m k t row hz hs
      have he : m+D.closure.edges.length+D.gArity*(t+1)=
          (m+D.closure.edges.length+D.gArity*t)+D.gArity := by simp [Nat.mul_add,Nat.add_assoc]
      have hc : D.gArity*count (row::rows)=D.gArity+D.gArity*count rows := by
        rw [count_cons,if_pos hz,Nat.mul_add,Nat.mul_one]
      simp only [emittedRows,ReplicationOrdinals.expand,hz,beq_self_eq_true,↓reduceIte,
        List.flatMap_cons,Nat.add_zero] at hic ⊢
      rw [hr,hc,edgeEnds_add]
      simp only [pending,if_neg htk,List.flatMap_cons,List.count_append] at hic hb ⊢
      rw [← he]
      omega
    · have hn : t+count rows=k := by simpa [count_cons,hz] using ht
      have hi := ih t hn
      apply List.perm_iff_count.mpr
      intro p
      have hic := hi.count_eq p
      simp only [emittedRows,ReplicationOrdinals.expand,hz,beq_iff_eq,↓reduceIte,
        Nat.add_zero,List.flatMap_cons,sourceRow,if_neg hz,count_cons,List.count_append,Nat.zero_add] at hic ⊢
      omega


theorem emitted_labels (m k t : ℕ) (rows : List RawVertex)
    (hw : ∀ row∈rows,row.1<D.count+1 ∧ row.2.length=D.sourceArity row.1) :
    ∀ row∈emittedRows D m k t rows,
      row.1<D.count+2 ∧ row.2.length=D.targetArity row.1 := by
  induction rows generalizing t with
  | nil => simp [emittedRows,ReplicationOrdinals.expand]
  | cons row rows ih =>
    have hh := hw row (by simp)
    have hi := ih (t+(if row.1==0 then 1 else 0)) (fun u hu => hw u (by simp [hu]))
    intro u hu
    simp only [emittedRows,ReplicationOrdinals.expand,List.mem_cons] at hu
    rcases hu with rfl|hu
    · by_cases hz : row.1=0
      · refine ⟨by simp [sourceRow,hz],?_⟩
        have hs : row.2.length=D.hArity := by simpa [Data.sourceArity,hz] using hh.2
        simp [sourceRow,hz,Data.targetArity,hs]
      · have hn : row.1≠D.count+1 := by omega
        refine ⟨by simpa [sourceRow,hz] using (show row.1<D.count+2 by omega),?_⟩
        simpa [sourceRow,hz,Data.targetArity,Data.carrierArity,Data.sourceArity,hn] using hh.2
    · exact hi u hu

theorem closure_labels (m k : ℕ)
    (hw : ∀ row∈D.closure.vertices,row.1<D.count+1 ∧ row.2.length=D.carrierArity row.1) :
    ∀ row∈D.closure.vertices.map (closureRow D m k),
      row.1<D.count+2 ∧ row.2.length=D.targetArity row.1 := by
  intro u hu
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hu
  have hh := hw row hr
  have hn : row.1≠D.count+1 := by omega
  refine ⟨by simpa [closureRow] using (show row.1<D.count+2 by omega),?_⟩
  by_cases hz : row.1=0
  · have hs : row.2.length=D.gArity := by simpa [Data.carrierArity,hz] using hh.2
    by_cases hk : k=0 <;> simp [closureRow,hz,hk,Data.targetArity,hn,Data.carrierArity,hs]
  · simpa [closureRow,hz,Data.targetArity,hn] using hh.2

theorem count_append (xs ys : List RawVertex) : count (xs++ys)=count xs+count ys := by
  simp [count]
theorem count_closure_rows (m k : ℕ) (rows : List RawVertex) :
    count (rows.map (closureRow D m k))=count rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [List.map_cons,count_cons,closureRow,ih]
theorem count_emitted (m k t : ℕ) (rows : List RawVertex) :
    count (emittedRows D m k t rows)=0 := by
  induction rows generalizing t with
  | nil => rfl
  | cons row rows ih =>
    by_cases hz : row.1=0 <;>
      simp [emittedRows,ReplicationOrdinals.expand,count_cons,sourceRow,hz,ih]

theorem query_one_marked (x : Input D) (hc : count D.closure.vertices=1) :
    occurrences 0 (query D x)=1 := by
  change count (query D x).vertices=1
  rw [query_vertices,count_append,count_closure_rows,count_emitted,hc]

theorem query_endpoints (x : Input D) (hc : count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts)
    (hl : D.seedPorts.length=D.gArity) :
    (query D x).endpoints.Perm
      (x.val.endpoints ++ D.closure.endpoints.map (shift x.val.edges.length) ++
        edgeEnds (x.val.edges.length+D.closure.edges.length) (D.gArity*count x.val.vertices)) := by
  have hv := query_vertices D x
  have he : (query D x).endpoints = closureEnds D x.val.edges.length (count x.val.vertices) D.closure.vertices ++
      (emittedRows D x.val.edges.length (count x.val.vertices) 0 x.val.vertices).flatMap Prod.snd := by
    rw [RawClosedNetwork.endpoints,hv]
    simp [closureEnds,List.flatMap]
  have hcl := closure_ends D x.val.edges.length (count x.val.vertices) hc hs
  have hco := closure_original_ends D x.val.edges.length hs
  have hp := emitted_partition D x.val.edges.length (count x.val.vertices) 0 x.val.vertices (by omega) hl
  apply List.perm_iff_count.mpr
  intro p
  have h₁ := hcl.count_eq p
  have h₂ := hco.count_eq p
  have h₃ := hp.count_eq p
  rw [he]
  simp only [List.count_append,RawClosedNetwork.endpoints,List.flatMap,pending,↓reduceIte,
    Nat.mul_zero,Nat.add_zero] at h₁ h₂ h₃ ⊢
  omega

theorem query_valid (x : Input D)
    (hw : D.closure.WellFormed (D.count+1) 1 D.carrierArity)
    (hc : count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts)
    (hl : D.seedPorts.length=D.gArity) :
    (query D x).WellFormed (D.count+2) 1 D.targetArity := by
  have H := (RawGrouping.wellFormed_iff_members _ _ _ _).mp x.property
  have Hc := (RawGrouping.wellFormed_iff_members _ _ _ _).mp hw
  apply (RawGrouping.wellFormed_iff_members _ _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro row hr
    rw [query_vertices] at hr
    rcases List.mem_append.mp hr with hr|hr
    · exact closure_labels D _ _ Hc.1 row hr
    · exact emitted_labels D _ _ _ _ H.1 row hr
  · intro e he
    simp only [query,List.mem_append,added_edges,List.mem_replicate] at he
    rcases he with (he|he)|⟨_,rfl⟩
    · exact H.2.1 e he
    · exact Hc.2.1 e he
    · decide
  · have hp := query_endpoints D x hc hs hl
    have hsource : x.val.endpoints.Perm (edgeEnds 0 x.val.edges.length) := by
      simpa only [expectedEndpoints_eq] using H.2.2
    have hclosure : (D.closure.endpoints.map (shift x.val.edges.length)).Perm
        (edgeEnds x.val.edges.length D.closure.edges.length) := by
      have h := Hc.2.2.map (shift x.val.edges.length)
      rw [expectedEndpoints_eq] at h
      change (D.closure.endpoints.map (shift x.val.edges.length)).Perm
        ((edgeEnds 0 D.closure.edges.length).map
          (fun p => (x.val.edges.length+p.1,p.2))) at h
      rw [edgeEnds_shift] at h
      exact h
    have ht := hsource.append (hclosure.append
      (List.Perm.refl (edgeEnds (x.val.edges.length+D.closure.edges.length) (D.gArity*count x.val.vertices))))
    have he := hp.trans (by simpa only [List.append_assoc] using ht)
    simpa only [expectedEndpoints_eq,query_edge_length,edgeEnds_add,Nat.zero_add,List.append_assoc] using he


end Paper2.Paper1Proved.ReplicationCompiler
