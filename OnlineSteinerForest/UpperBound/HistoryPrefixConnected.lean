import OnlineSteinerForest.UpperBound.HistoryPayments

/-! Every completed request is connected in all subsequent purchased graphs. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem request_reachable_after (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (j : Fin requests.length) (i : ℕ) (hji : j.val < i) :
    (SimpleGraph.fromEdgeSet (boughtBefore G c requests feasible i : Set (Sym2 V))).Reachable
      requests[j.val].1 requests[j.val].2 := by
  apply reachable_mono_edges (boughtBefore_mono G c requests feasible (j.val + 1) i (by omega))
  rw [boughtBefore_succ]
  exact reachable_mono_edges Finset.subset_union_right
    (shortestPathEdges_spec G c (boughtBefore G c requests feasible j.val)
      requests[j.val].1 requests[j.val].2 (feasible _ (List.getElem_mem j.isLt))).1.reachable

end OnlineSteinerForest.UpperBound
