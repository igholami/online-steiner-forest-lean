import OnlineSteinerForest.UpperBound.NearestNeighborInsertionPacking
import OnlineSteinerForest.UpperBound.NearestNeighborOrderStatistics

/-! The nearest-earlier-vertex bound for a finite weighted tree (manuscript Lemma 4.4). -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

theorem nearest_neighbor_sum (G : SimpleGraph V) (hG : G.IsTree) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (x : Fin (n + 1) → V) :
    (∑ i : Fin n, insertionDistance G c hG.connected.preconnected x i) ≤
      2 * edgeCost c G.edgeFinset * Real.log ((n + 1 : ℕ) : ℝ) := by
  apply sum_le_log_of_threshold_packing n _ _
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun e he => hc e (G.mem_edgeFinset.mp he)))
  · exact insertionDistance_nonneg G c hc hG.connected.preconnected x
  · exact insertion_threshold_packing G hG c hc x

end OnlineSteinerForest.UpperBound
