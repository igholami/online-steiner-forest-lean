import OnlineSteinerForest.UpperBound.NearestNeighborLabel
import OnlineSteinerForest.UpperBound.NearestNeighborParameter

/-! Actual label-batch insertion lengths in the manuscript's common logarithmic parameter. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem nearest_neighbor_label_pairLog (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) :
    ∑ j : Fin n, insertionDistance (lifetimeComponent G c requests feasible fallback label).toSimpleGraph
      (fun e => c (Sym2.map Subtype.val e))
      (lifetimeComponent G c requests feasible fallback label).connected_toSimpleGraph.preconnected
      (labelFarSequence G c hc requests feasible fallback batch label hcard) j ≤
      2 * cycleFactor requests.length * clusterWeight (blockPayment G c requests feasible)
        (finalLifetime G c requests feasible label) := by
  have hnk : n + 1 ≤ requests.length := by
    rw [← hcard]
    simpa only [Fintype.card_fin] using Finset.card_le_univ (s := labelBatch G c requests feasible batch label)
  have hlog := log_card_le_pairLog (n + 1) requests.length (by omega) hnk
  have hw : 0 ≤ clusterWeight (blockPayment G c requests feasible) (finalLifetime G c requests feasible label) :=
    Finset.sum_nonneg (fun a ha => blockPayment_nonneg G c (fun e he => le_of_lt (hc e he)) requests feasible a)
  apply (nearest_neighbor_label_batch G c hc requests feasible fallback batch label hcard).trans
  calc
    _ ≤ 2 * clusterWeight (blockPayment G c requests feasible) (finalLifetime G c requests feasible label) *
        cycleFactor requests.length := mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num) hw)
    _ = _ := by ring

end OnlineSteinerForest.UpperBound
