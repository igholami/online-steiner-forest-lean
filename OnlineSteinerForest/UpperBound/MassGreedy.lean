import OnlineSteinerForest.UpperBound.HistoryGreedy

/-! Lifetime payment mass for the actual greedy component-label computation. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_positive_blocks_eq_greedyCost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    ∑ i ∈ scannedBlocks (fun j => 0 < blockPayment G c requests feasible j) requests.length,
      blockPayment G c requests feasible i = greedyCost G c requests feasible := by
  rw [scannedBlocks, Finset.sum_filter]
  calc
    _ = ∑ i ∈ Finset.range requests.length, blockPayment G c requests feasible i := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with hpos
      · rfl
      · exact (le_antisymm (le_of_not_gt hpos)
          (blockPayment_nonneg G c hc requests feasible i)).symm
    _ = _ := sum_blockPayments G c requests feasible

/-- Each paid edge block is counted once for the surviving lifetime and once for
each retired ancestor; union-by-size bounds that number logarithmically. -/
theorem greedy_lifetime_mass (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    lifetimeMass (greedyHistory G c requests feasible requests.length)
      (blockPayment G c requests feasible) ≤
      (((scannedBlocks (fun j => 0 < blockPayment G c requests feasible j)
        requests.length).card.log2 : ℝ) + 1) * greedyCost G c requests feasible := by
  have hm := scanHistory_mass (fun j => 0 < blockPayment G c requests feasible j)
    (touchesBlock G c requests feasible) (blockPayment G c requests feasible)
    (fun _ h => le_of_lt h) requests.length
  rw [sum_positive_blocks_eq_greedyCost G c hc requests feasible] at hm
  exact hm

end OnlineSteinerForest.UpperBound
