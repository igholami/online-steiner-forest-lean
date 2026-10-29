import OnlineSteinerForest.UpperBound.HistoryMergedComponent
import OnlineSteinerForest.UpperBound.HistoryRequestLabels

/-! A birth request's selected path contains only newly purchased edges. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem birth_path_eq_block (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hb : isBirth G c requests feasible i.val) :
    shortestPathEdges G c (boughtBefore G c requests feasible i.val)
      requests[i.val].1 requests[i.val].2 (feasible _ (List.getElem_mem i.isLt)) =
        purchasedBlock G c requests feasible i.val := by
  apply Finset.Subset.antisymm
  · obtain ⟨p, hp, heq⟩ := (shortestPathEdges_spec G c (boughtBefore G c requests feasible i.val)
      requests[i.val].1 requests[i.val].2 (feasible _ (List.getElem_mem i.isLt))).1
    intro e he
    have heP : e ∈ p.edges := by apply List.mem_toFinset.mp; simpa only [heq] using he
    have hsub : p.edges.toFinset ⊆ boughtBefore G c requests feasible (i.val + 1) := by
      rw [boughtBefore_succ, heq]
      exact Finset.subset_union_right
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hu := reachable_mono_edges hsub (walk_support_reachable p u (p.fst_mem_support_of_mem_edges heP))
      have hm := after_component_edge_mem_merged G c hc requests feasible i u v
        (hsub (List.mem_toFinset.mpr heP)) hu
      change s(u, v) ∈ clusterEdges G c requests feasible (MergeHistory.merged i.val (touchedAt G c requests feasible i.val)) at hm
      rw [merged_clusterEdges, show touchedAt G c requests feasible i.val = ∅ from hb] at hm
      simpa only [Finset.biUnion_empty, Finset.union_empty] using hm
  · exact purchasedBlock_subset_path G c requests feasible i

theorem birth_path_original_cost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hb : isBirth G c requests feasible i.val) :
    edgeCost c (shortestPathEdges G c (boughtBefore G c requests feasible i.val)
      requests[i.val].1 requests[i.val].2 (feasible _ (List.getElem_mem i.isLt))) = payment G c requests feasible i := by
  rw [birth_path_eq_block G c hc requests feasible i hb, purchasedBlock_cost]

end OnlineSteinerForest.UpperBound
