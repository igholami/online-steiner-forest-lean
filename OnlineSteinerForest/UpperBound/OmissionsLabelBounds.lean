import OnlineSteinerForest.UpperBound.OmissionsLabelAlgorithm
import OnlineSteinerForest.UpperBound.AuxiliaryLifetimeWeights

/-! Per-label payment bounds for the computed first and long omissions. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem first_label_payment_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) :
    (64 * (cycleFactor requests.length : ℝ) ^ 2) *
      ∑ j ∈ firstLabelPositions G c requests feasible batch label hcard,
        blockPayment G c requests feasible (orderedLabelRequest G c requests feasible batch label hcard j).val ≤
      clusterWeight (blockPayment G c requests feasible) (finalLifetime G c requests feasible label) := by
  unfold firstLabelPositions
  rw [Finset.filter_singleton]
  split_ifs with hfirst
  · simpa only [Finset.sum_singleton] using le_of_lt hfirst
  · simp only [Finset.sum_empty, mul_zero]
    exact Finset.sum_nonneg (fun a ha => blockPayment_nonneg G c hc requests feasible a)

theorem labelProxyLength_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (j : Fin n) :
    0 ≤ labelProxyLength G c hc requests feasible fallback batch label hcard j :=
  insertionDistance_nonneg _ _ (lifetimeComponent_weights_nonneg G c (fun e he => le_of_lt (hc e he))
    requests feasible fallback label) _ _ j

theorem long_label_payment_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (scale : ℝ)
    (hbatch : ∀ i ∈ batch, blockPayment G c requests feasible i.val ≤ 2 * scale) :
    (128 * (cycleFactor requests.length : ℝ) ^ 3) *
      ∑ j ∈ longLabelPositions G c hc requests feasible fallback batch label hcard scale,
        blockPayment G c requests feasible (orderedLabelRequest G c requests feasible batch label hcard (newIndex j)).val ≤
      2 * cycleFactor requests.length * clusterWeight (blockPayment G c requests feasible)
        (finalLifetime G c requests feasible label) := by
  have hL : 0 ≤ (cycleFactor requests.length : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ∑ j ∈ longLabelPositions G c hc requests feasible fallback batch label hcard scale,
        labelProxyLength G c hc requests feasible fallback batch label hcard j := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hd := (Finset.mem_filter.mp hj).2.1
      have hm := (Finset.mem_filter.mp
        (orderedLabelRequest_mem G c requests feasible batch label hcard (newIndex j))).1
      have hp := hbatch _ hm
      have hmul := mul_le_mul_of_nonneg_left hp
        (by positivity : 0 ≤ 128 * (cycleFactor requests.length : ℝ) ^ 3)
      nlinarith
    _ ≤ ∑ j : Fin n, labelProxyLength G c hc requests feasible fallback batch label hcard j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => labelProxyLength_nonneg G c hc requests feasible fallback batch label hcard j)
    _ ≤ _ := nearest_neighbor_label_pairLog G c hc requests feasible fallback batch label hcard

end OnlineSteinerForest.UpperBound
