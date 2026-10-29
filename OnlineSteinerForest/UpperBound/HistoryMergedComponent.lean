import OnlineSteinerForest.UpperBound.HistoryEdgeRepresentatives
import OnlineSteinerForest.UpperBound.HistoryCover

/-! A newly merged snapshot contains the entire actual request component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem after_component_edge_mem_merged (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (u v : V) (he : s(u, v) ∈ boughtBefore G c requests feasible (i.val + 1))
    (hreach : (SimpleGraph.fromEdgeSet
      (boughtBefore G c requests feasible (i.val + 1) : Set (Sym2 V))).Reachable requests[i.val].1 u) :
    s(u, v) ∈ clusterEdges G c requests feasible
      (MergeHistory.merged i.val ((greedyHistory G c requests feasible i.val).active.filter
        (touchesBlock G c requests feasible i.val))) := by
  by_cases hold : s(u, v) ∈ boughtBefore G c requests feasible i.val
  · rw [← greedyHistory_covers G c hc requests feasible i.val (Nat.le_of_lt i.isLt)] at hold
    obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.mp hold
    have hconn := (cluster_edge_connected_to_label G c requests feasible i.val (Nat.le_of_lt i.isLt)
      C hC u v heC).1
    have hnext := reachable_mono_edges
      (boughtBefore_mono G c requests feasible i.val (i.val + 1) (by omega)) hconn
    have hlabel := (greedyHistory_invariant G c requests feasible i.val).partition.label_mem C hC
    have hlabelLt := greedyHistory_snapshot_members G c requests feasible i.val C (Or.inl hC) C.label hlabel
    have hlabelLen : C.label < requests.length := hlabelLt.trans i.isLt
    have ht : C ∈ (greedyHistory G c requests feasible i.val).active.filter
        (touchesBlock G c requests feasible i.val) := by
      refine Finset.mem_filter.mpr ⟨hC, i.isLt, hlabelLen, ?_⟩
      simpa only [requestSource_eq requests u C.label hlabelLen] using hreach.trans hnext.symm
    exact touched_clusterEdges_subset G c requests feasible i.val _ C ht heC
  · rw [merged_clusterEdges]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he, hold⟩)

/-- Actual request-component connections are realized inside the merged snapshot itself. -/
theorem after_component_reachable_in_merged (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length) (v : V)
    (hv : (SimpleGraph.fromEdgeSet
      (boughtBefore G c requests feasible (i.val + 1) : Set (Sym2 V))).Reachable requests[i.val].1 v) :
    (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible
      (MergeHistory.merged i.val ((greedyHistory G c requests feasible i.val).active.filter
        (touchesBlock G c requests feasible i.val))) : Set (Sym2 V))).Reachable requests[i.val].1 v := by
  obtain ⟨q⟩ := hv
  apply walk_reachable_fromEdgeSet q
  intro e he
  induction e using Sym2.inductionOn with
  | _ u w =>
    have heB : s(u, w) ∈ boughtBefore G c requests feasible (i.val + 1) := by
      have heG := q.edges_subset_edgeSet he
      have heG' : s(u, w) ∈ (boughtBefore G c requests feasible (i.val + 1) : Set (Sym2 V)) \ Sym2.diagSet := by
        simpa only [SimpleGraph.edgeSet_fromEdgeSet] using heG
      exact heG'.1
    exact after_component_edge_mem_merged G c hc requests feasible i u w heB
      ⟨q.takeUntil u (q.fst_mem_support_of_mem_edges he)⟩

end OnlineSteinerForest.UpperBound
