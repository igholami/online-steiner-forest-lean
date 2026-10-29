import OnlineSteinerForest.UpperBound.HistoryBlocks
import OnlineSteinerForest.UpperBound.AuxiliaryAfterStep

/-! Every purchased block lies in its request's actual bought component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem purchasedBlock_subset_path (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (j : Fin requests.length) :
    purchasedBlock G c requests feasible j.val ⊆
      shortestPathEdges G c (boughtBefore G c requests feasible j.val)
        requests[j.val].1 requests[j.val].2 (feasible _ (List.getElem_mem j.isLt)) := by
  intro e he
  rw [purchasedBlock, boughtBefore_succ] at he
  exact (Finset.mem_union.mp (Finset.mem_sdiff.mp he).1).resolve_left (Finset.mem_sdiff.mp he).2

theorem purchasedBlock_vertices_connected (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (j : Fin requests.length) (i : ℕ) (hji : j.val < i) (u v : V)
    (he : s(u, v) ∈ purchasedBlock G c requests feasible j.val) :
    (SimpleGraph.fromEdgeSet (boughtBefore G c requests feasible i : Set (Sym2 V))).Reachable requests[j.val].1 u ∧
    (SimpleGraph.fromEdgeSet (boughtBefore G c requests feasible i : Set (Sym2 V))).Reachable requests[j.val].1 v := by
  obtain ⟨p, hp, heq⟩ := (shortestPathEdges_spec G c (boughtBefore G c requests feasible j.val)
    requests[j.val].1 requests[j.val].2 (feasible _ (List.getElem_mem j.isLt))).1
  have hep : s(u, v) ∈ p.edges := by
    apply List.mem_toFinset.mp
    rw [heq]
    exact purchasedBlock_subset_path G c requests feasible j he
  have hsub : p.edges.toFinset ⊆ boughtBefore G c requests feasible i := by
    apply Finset.Subset.trans _ (boughtBefore_mono G c requests feasible (j.val + 1) i (by omega))
    rw [boughtBefore_succ, heq]
    exact Finset.subset_union_right
  exact ⟨reachable_mono_edges hsub (walk_support_reachable p u (p.fst_mem_support_of_mem_edges hep)),
    reachable_mono_edges hsub (walk_support_reachable p v (p.snd_mem_support_of_mem_edges hep))⟩

end OnlineSteinerForest.UpperBound
