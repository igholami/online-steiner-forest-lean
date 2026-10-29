import OnlineSteinerForest.LowerBound.GreedyRun
import OnlineSteinerForest.LowerBound.Instance

/-! Exact total cost of greedy on the manuscript's retained good ranks. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

variable {m : ℕ}

theorem matching_union_cost (σ : Equiv.Perm (Fin (2 * m))) (w : Fin m → ℝ)
    (R : Finset (Fin m)) :
    edgeCost (constructionCost w) (R.biUnion (matchingEdges σ)) = ∑ i ∈ R, w i := by
  rw [edgeCost, Finset.sum_biUnion (fun i _ j _ hij => matchingEdges_disjoint σ hij)]
  exact Finset.sum_congr rfl (fun i _ => matchingEdges_cost σ w i)

theorem greedy_on_good_ranks (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (R : Finset (Fin (matchingSize h))) (hgood : ∀ i ∈ R, GoodRank h σ i) :
    greedy (constructionGraph σ R) (constructionCost (rankPrice h))
      (requestedPairs σ R) (requestedPairs_feasible σ R) = R.biUnion (matchingEdges σ) := by
  have hg := greedy_rank_list h σ R (R.sort (· ≤ ·))
    (fun i hi => (Finset.mem_sort (· ≤ ·)).mp hi)
    (fun i hi => hgood i ((Finset.mem_sort (· ≤ ·)).mp hi))
    R.sortedLT_sort.pairwise ∅ (by simp) (requestedPairs_feasible σ R)
  simpa only [rankRequests, requestedPairs, Finset.biUnion_empty,
    Finset.empty_union, Finset.sort_toFinset] using hg

theorem instance_greedy_edges (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    greedy (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
      (instance_feasible h σ) = (retainedRanks h σ).biUnion (matchingEdges σ) := by
  classical
  exact greedy_on_good_ranks h σ _ (fun i hi => (Finset.mem_filter.mp hi).2.2)

theorem instance_greedy_cost (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    greedyCost (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
      (instance_feasible h σ) = ∑ i ∈ retainedRanks h σ, rankPrice h i := by
  rw [greedyCost, instance_greedy_edges, matching_union_cost]

theorem instance_greedy_cost_ge_half (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (hσ : RetainsHalf h σ) :
    totalPrice h / 2 ≤ greedyCost (instanceGraph h σ) (constructionCost (rankPrice h))
      (instanceRequests h σ) (instance_feasible h σ) := by
  rw [instance_greedy_cost]
  exact hσ

end OnlineSteinerForest.LowerBound
